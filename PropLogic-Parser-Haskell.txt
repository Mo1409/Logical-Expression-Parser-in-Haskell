import Data.Char (isAlpha, isAlphaNum)
import Data.Maybe (fromMaybe)
import Data.List (intercalate, nub)
import Data.Foldable (foldlM)
import Control.Monad (replicateM)
import Data.Function (on)
import Data.Map (Map)
import Data.Char (isAlpha, isAlphaNum, toLower)
import qualified Data.Map as Map

-- Define o tipo de dados TokenType para representar os diferentes tipos de tokens possíveis
data TokenType = LPAREN          -- Parêntese esquerdo '('
               | RPAREN          -- Parêntese direito ')'
               | AND             -- Operador lógico E '^'
               | OR              -- Operador lógico OU 'v'
               | NOT             -- Operador de negação '~'
               | FORALL          -- Quantificador universal '∀'
               | EXISTS          -- Quantificador existencial '∃'
               | IMPLIES         -- Operador de implicação '->'
               | BICOND          -- Operador bicondicional '<->'
               | IDENT String    -- Identificador, armazenando uma string (nomes de variáveis ou constantes)
               deriving (Show, Eq) -- Permite que TokenType seja exibido e comparado

-- Define o tipo de dados Token, que armazena um TokenType e o texto original do token
data Token = Token TokenType String deriving (Show, Eq)

-- Define os nós da árvore de expressão para representar a estrutura das fórmulas
data Node
    = BinaryNode String Node Node      -- Nó binário com um operador e dois nós filhos (ex: AND, OR)
    | UnaryNode String Node            -- Nó unário com um operador e um nó filho (ex: NOT)
    | QuantifiedNode String String Node-- Nó de quantificação com o quantificador, a variável e um nó filho
    | LeafNode String                  -- Nó folha que representa um identificador ou valor terminal
    deriving (Show, Eq)

-- Função de tokenização, converte uma string de entrada em uma lista de tokens
tokenize :: String -> [Token]
tokenize [] = []  -- Caso base: uma string vazia resulta em uma lista vazia de tokens

-- Processa cada caractere da string de entrada
tokenize (c:cs)
    -- Ignora espaços e tabulações
    | c == ' ' || c == '\t' = tokenize cs

    -- Identifica e armazena o parêntese esquerdo
    | c == '(' = Token LPAREN "(" : tokenize cs

    -- Identifica e armazena o parêntese direito
    | c == ')' = Token RPAREN ")" : tokenize cs

    -- Identifica e armazena o operador lógico AND ('^')
    | c == '^' = Token AND "^" : tokenize cs

    -- Identifica e armazena o operador lógico OR ('v')
    | c == 'v' = Token OR "v" : tokenize cs

    -- Identifica e armazena o operador de negação ('~')
    | c == '~' = Token NOT "~" : tokenize cs

    -- Identifica e armazena o quantificador universal ('∀')
    | c == '∀' = Token FORALL "∀" : tokenize cs

    -- Identifica e armazena o quantificador existencial ('∃')
    | c == '∃' = Token EXISTS "∃" : tokenize cs

    -- Identifica e armazena o operador de implicação ('->')
    | c == '-' && not (null cs) && head cs == '>' = Token IMPLIES "->" : tokenize (tail cs)

    -- Identifica e armazena o operador bicondicional ('<->')
    | c == '<' && length cs >= 2 && cs !! 0 == '-' && cs !! 1 == '>' = Token BICOND "<->" : tokenize (drop 2 cs)

    -- Identifica identificadores (variáveis ou constantes)
    | isAlpha c =
        let (ident, rest) = span (\x -> isAlphaNum x || x == '_') (c:cs) -- Coleta todos os caracteres válidos do identificador
        in Token (IDENT ident) ident : tokenize rest -- Cria um token IDENT e continua a tokenização com o resto da string

    -- Caso o caractere não seja reconhecido, gera um erro
    | otherwise = error $ "Unknown character: " ++ [c]


-- Define o tipo Parser, que representa uma função que recebe uma lista de tokens
-- e retorna um resultado do tipo Either (que pode conter um erro ou um nó da árvore e tokens restantes)
type Parser = [Token] -> Either String (Node, [Token])

-- Função 'peek' para visualizar o primeiro token (caso exista) sem removê-lo
peek :: [Token] -> Maybe Token
peek [] = Nothing            -- Retorna Nothing se a lista de tokens está vazia
peek (t:_) = Just t          -- Retorna o primeiro token como Just t

-- Função 'match' para verificar se o próximo token é do tipo esperado
match :: TokenType -> [Token] -> Either String (Token, [Token])
match expectedType tokens = case tokens of
    (t@(Token typ _):rest) | typ == expectedType -> Right (t, rest)  -- Se o tipo do token corresponde ao esperado, retorna ele e os tokens restantes
    _ -> Left $ "Token mismatch: expected " ++ show expectedType     -- Caso contrário, retorna um erro indicando o tipo esperado

-- Função principal do parser de expressões
parseExpression :: Parser
parseExpression tokens = parseBiconditional tokens  -- Começa tentando analisar uma expressão bicondicional

-- Função para analisar uma expressão bicondicional
parseBiconditional :: Parser
parseBiconditional tokens = do
    (leftNode, tokens1) <- parseImplication tokens     -- Analisa o lado esquerdo da expressão (implicação)
    case peek tokens1 of                               -- Verifica se o próximo token é um bicondicional
        Just (Token BICOND _) -> do
            (_, tokens2) <- match BICOND tokens1       -- Confirma o operador bicondicional e avança
            (rightNode, tokens3) <- parseImplication tokens2  -- Analisa o lado direito da implicação
            return (BinaryNode "<->" leftNode rightNode, tokens3) -- Retorna um nó binário "<->" com os nós esquerdo e direito
        _ -> return (leftNode, tokens1)                -- Se não for bicondicional, retorna apenas o nó esquerdo

-- Função para analisar uma expressão de implicação
parseImplication :: Parser
parseImplication tokens = do
    (leftNode, tokens1) <- parseDisjunction tokens     -- Analisa o lado esquerdo da disjunção
    case peek tokens1 of                               -- Verifica se o próximo token é uma implicação
        Just (Token IMPLIES _) -> do
            (_, tokens2) <- match IMPLIES tokens1      -- Confirma o operador de implicação e avança
            (rightNode, tokens3) <- parseImplication tokens2  -- Analisa recursivamente o lado direito
            return (BinaryNode "->" leftNode rightNode, tokens3) -- Retorna um nó binário "->"
        _ -> return (leftNode, tokens1)                -- Se não for implicação, retorna o nó esquerdo

-- Função para analisar uma expressão de disjunção (OR)
parseDisjunction :: Parser
parseDisjunction tokens = do
    (leftNode, tokens1) <- parseConjunction tokens     -- Analisa o lado esquerdo da conjunção
    parseDisjunction' leftNode tokens1                 -- Continua a análise com parseDisjunction' para identificar cadeias de disjunções

-- Função auxiliar para analisar disjunções contínuas (OR) em sequência
parseDisjunction' :: Node -> [Token] -> Either String (Node, [Token])
parseDisjunction' leftNode tokens = case peek tokens of
    Just (Token OR _) -> do
        (_, tokens1) <- match OR tokens                -- Confirma o operador OR e avança
        (rightNode, tokens2) <- parseConjunction tokens1 -- Analisa o lado direito da conjunção
        let newLeftNode = BinaryNode "v" leftNode rightNode -- Cria um novo nó binário "v" com os nós esquerdo e direito
        parseDisjunction' newLeftNode tokens2          -- Continua a análise para mais disjunções
    _ -> return (leftNode, tokens)                     -- Se não houver mais disjunções, retorna o nó resultante

-- Função para analisar uma expressão de conjunção (AND)
parseConjunction :: Parser
parseConjunction tokens = do
    (leftNode, tokens1) <- parseNegation tokens        -- Analisa o lado esquerdo da negação
    parseConjunction' leftNode tokens1                 -- Continua a análise com parseConjunction' para identificar cadeias de conjunções

-- Função auxiliar para analisar conjunções contínuas (AND) em sequência
parseConjunction' :: Node -> [Token] -> Either String (Node, [Token])
parseConjunction' leftNode tokens = case peek tokens of
    Just (Token AND _) -> do
        (_, tokens1) <- match AND tokens               -- Confirma o operador AND e avança
        (rightNode, tokens2) <- parseNegation tokens1  -- Analisa o lado direito da negação
        let newLeftNode = BinaryNode "^" leftNode rightNode -- Cria um novo nó binário "^" com os nós esquerdo e direito
        parseConjunction' newLeftNode tokens2          -- Continua a análise para mais conjunções
    _ -> return (leftNode, tokens)                     -- Se não houver mais conjunções, retorna o nó resultante

-- Função para analisar uma expressão de negação (NOT)
parseNegation :: Parser
parseNegation tokens = case peek tokens of
    Just (Token NOT _) -> do
        (_, tokens1) <- match NOT tokens               -- Confirma o operador NOT e avança
        (operandNode, tokens2) <- parseNegation tokens1 -- Analisa recursivamente o operando da negação
        return (UnaryNode "~" operandNode, tokens2)    -- Retorna um nó unário "~" com o operando
    _ -> parseQuantified tokens                        -- Caso não seja uma negação, tenta analisar uma expressão quantificada

-- Função para analisar uma expressão quantificada (FORALL ou EXISTS)
parseQuantified :: Parser
parseQuantified tokens = case peek tokens of
    Just (Token FORALL _) -> do
        (_, tokens1) <- match FORALL tokens            -- Confirma o quantificador FORALL e avança
        case match (IDENT "") tokens1 of               -- Tenta obter a variável de quantificação
            Left err -> Left err                       -- Retorna erro se a variável estiver ausente
            Right (Token (IDENT var) _, tokens2) -> do
                (exprNode, tokens3) <- parseExpression tokens2 -- Analisa a expressão quantificada
                return (QuantifiedNode "∀" var exprNode, tokens3) -- Retorna um nó de quantificação universal
    Just (Token EXISTS _) -> do
        (_, tokens1) <- match EXISTS tokens            -- Confirma o quantificador EXISTS e avança
        case match (IDENT "") tokens1 of               -- Tenta obter a variável de quantificação
            Left err -> Left err                       -- Retorna erro se a variável estiver ausente
            Right (Token (IDENT var) _, tokens2) -> do
                (exprNode, tokens3) <- parseExpression tokens2 -- Analisa a expressão quantificada
                return (QuantifiedNode "∃" var exprNode, tokens3) -- Retorna um nó de quantificação existencial
    _ -> parseAtomic tokens                            -- Se não for uma expressão quantificada, tenta analisar uma expressão atômica

-- Função para analisar uma expressão atômica (um identificador ou uma subexpressão entre parênteses)
parseAtomic :: Parser
parseAtomic tokens = case peek tokens of
    Just (Token LPAREN _) -> do
        (_, tokens1) <- match LPAREN tokens            -- Confirma o parêntese esquerdo e avança
        (exprNode, tokens2) <- parseExpression tokens1 -- Analisa a expressão dentro dos parênteses
        (_, tokens3) <- match RPAREN tokens2           -- Confirma o parêntese direito e avança
        return (exprNode, tokens3)                     -- Retorna a expressão entre parênteses
    Just (Token (IDENT ident) _) -> do
        (_, tokens1) <- match (IDENT ident) tokens     -- Confirma o identificador e avança
        return (LeafNode ident, tokens1)               -- Retorna um nó folha com o identificador
    _ -> Left "Expected atomic expression"             -- Retorna erro se não houver expressão atômica válida



-- Função que elimina bicondicionais na árvore de expressão
eliminateBiconditionals :: Node -> Node
eliminateBiconditionals node = case node of
    -- Se o nó é um bicondicional ("<->"), o transforma em uma conjunção de duas implicações
    -- Exemplo: A <-> B se torna (A -> B) ^ (B -> A)
    BinaryNode "<->" left right ->
        let leftImp = eliminateBiconditionals (BinaryNode "->" left right)
            rightImp = eliminateBiconditionals (BinaryNode "->" right left)
        in BinaryNode "^" leftImp rightImp
    -- Caso contrário, aplica recursivamente aos nós filhos
    BinaryNode op left right ->
        BinaryNode op (eliminateBiconditionals left) (eliminateBiconditionals right)
    UnaryNode op operand ->
        UnaryNode op (eliminateBiconditionals operand)
    QuantifiedNode quant var expr ->
        QuantifiedNode quant var (eliminateBiconditionals expr)
    _ -> node -- Para LeafNode, apenas retorna o nó

-- Função que elimina implicações na árvore de expressão
eliminateImplications :: Node -> Node
eliminateImplications node = case node of
    -- Se o nó é uma implicação ("->"), a transforma em uma disjunção
    -- Exemplo: A -> B se torna ~A v B
    BinaryNode "->" left right ->
        let newLeft = eliminateImplications (UnaryNode "~" left)
            newRight = eliminateImplications right
        in BinaryNode "v" newLeft newRight
    -- Caso contrário, aplica recursivamente aos nós filhos
    BinaryNode op left right ->
        BinaryNode op (eliminateImplications left) (eliminateImplications right)
    UnaryNode op operand ->
        UnaryNode op (eliminateImplications operand)
    QuantifiedNode quant var expr ->
        QuantifiedNode quant var (eliminateImplications expr)
    _ -> node

-- Função que move negações para dentro da árvore de expressão
moveNegationInwards :: Node -> Node
moveNegationInwards node = case node of
    -- Caso seja uma negação, aplica as regras de De Morgan e outros casos de negação
    UnaryNode "~" operand -> case operand of
        -- ~~A se torna A (elimina a dupla negação)
        UnaryNode "~" grandchild ->
            moveNegationInwards grandchild
        -- ~(A ^ B) se torna ~A v ~B
        BinaryNode "^" left right ->
            let newLeft = moveNegationInwards (UnaryNode "~" left)
                newRight = moveNegationInwards (UnaryNode "~" right)
            in BinaryNode "v" newLeft newRight
        -- ~(A v B) se torna ~A ^ ~B
        BinaryNode "v" left right ->
            let newLeft = moveNegationInwards (UnaryNode "~" left)
                newRight = moveNegationInwards (UnaryNode "~" right)
            in BinaryNode "^" newLeft newRight
        -- ~∀x. A se torna ∃x. ~A
        QuantifiedNode "∀" var expr ->
            let newExpr = moveNegationInwards (UnaryNode "~" expr)
            in QuantifiedNode "∃" var newExpr
        -- ~∃x. A se torna ∀x. ~A
        QuantifiedNode "∃" var expr ->
            let newExpr = moveNegationInwards (UnaryNode "~" expr)
            in QuantifiedNode "∀" var newExpr
        -- Caso contrário, aplica a negação recursivamente
        _ ->
            UnaryNode "~" (moveNegationInwards operand)
    -- Aplica recursivamente a todos os nós filhos
    BinaryNode op left right ->
        BinaryNode op (moveNegationInwards left) (moveNegationInwards right)
    QuantifiedNode quant var expr ->
        QuantifiedNode quant var (moveNegationInwards expr)
    _ -> node

-- Função que distribui disjunções sobre conjunções para normalizar a árvore de expressão
distributeOrOverAnd :: Node -> Node
distributeOrOverAnd node = case node of
    -- Caso seja uma disjunção (v), tenta distribuir sobre conjunções
    BinaryNode "v" left right ->
        let newLeft = distributeOrOverAnd left
            newRight = distributeOrOverAnd right
        in case (newLeft, newRight) of
            -- A v (B ^ C) se torna (A v B) ^ (A v C)
            (BinaryNode "^" a b, _) ->
                let left1 = distributeOrOverAnd (BinaryNode "v" a newRight)
                    left2 = distributeOrOverAnd (BinaryNode "v" b newRight)
                in BinaryNode "^" left1 left2
            -- (A ^ B) v C se torna (A v C) ^ (B v C)
            (_, BinaryNode "^" a b) ->
                let right1 = distributeOrOverAnd (BinaryNode "v" newLeft a)
                    right2 = distributeOrOverAnd (BinaryNode "v" newLeft b)
                in BinaryNode "^" right1 right2
            -- Caso contrário, apenas retorna a disjunção
            _ ->
                BinaryNode "v" newLeft newRight
    -- Aplica recursivamente a todos os nós filhos
    BinaryNode op left right ->
        BinaryNode op (distributeOrOverAnd left) (distributeOrOverAnd right)
    UnaryNode op operand ->
        UnaryNode op (distributeOrOverAnd operand)
    QuantifiedNode quant var expr ->
        QuantifiedNode quant var (distributeOrOverAnd expr)
    _ -> node

-- Função que elimina negações duplas na árvore de expressão
eliminateDoubleNegations :: Node -> Node
eliminateDoubleNegations node = case node of
    -- Se houver uma dupla negação (~~A), a elimina
    UnaryNode "~" (UnaryNode "~" operand) ->
        eliminateDoubleNegations operand
    -- Caso contrário, aplica recursivamente
    UnaryNode op operand ->
        UnaryNode op (eliminateDoubleNegations operand)
    BinaryNode op left right ->
        BinaryNode op (eliminateDoubleNegations left) (eliminateDoubleNegations right)
    QuantifiedNode quant var expr ->
        QuantifiedNode quant var (eliminateDoubleNegations expr)
    _ -> node

-- Função que verifica se uma variável é livre (não quantificada) em uma expressão
isVariableFree :: Node -> String -> Bool
isVariableFree node variable = case node of
    -- Se é um nó quantificado, verifica se a variável é igual ao nome do quantificador
    QuantifiedNode _ var expr ->
        if var == variable then False else isVariableFree expr variable
    -- Caso seja uma variável folha, verifica se ela é a procurada
    LeafNode varName ->
        varName == variable
    -- Aplica recursivamente nos nós filhos
    BinaryNode _ left right ->
        isVariableFree left variable || isVariableFree right variable
    UnaryNode _ operand ->
        isVariableFree operand variable
    _ -> False

-- Função que elimina quantificadores universais que não afetam a expressão
eliminateUniversalQuantifiers :: Node -> Node
eliminateUniversalQuantifiers node = case node of
    QuantifiedNode "∀" var expr ->
        if not (isVariableFree expr var)
        then eliminateUniversalQuantifiers expr -- Elimina se não for livre na expressão
        else QuantifiedNode "∀" var (eliminateUniversalQuantifiers expr)
    -- Aplica recursivamente aos nós filhos
    BinaryNode op left right ->
        BinaryNode op (eliminateUniversalQuantifiers left) (eliminateUniversalQuantifiers right)
    UnaryNode op operand ->
        UnaryNode op (eliminateUniversalQuantifiers operand)
    _ -> node

-- Função que elimina quantificadores existenciais que não afetam a expressão
eliminateExistentialQuantifiers :: Node -> Node
eliminateExistentialQuantifiers node = case node of
    QuantifiedNode "∃" var expr ->
        if not (isVariableFree expr var)
        then eliminateExistentialQuantifiers expr -- Elimina se não for livre na expressão
        else QuantifiedNode "∃" var (eliminateExistentialQuantifiers expr)
    -- Aplica recursivamente aos nós filhos
    BinaryNode op left right ->
        BinaryNode op (eliminateExistentialQuantifiers left) (eliminateExistentialQuantifiers right)
    UnaryNode op operand ->
        UnaryNode op (eliminateExistentialQuantifiers operand)
    _ -> node

-- Função que move quantificadores para fora da expressão
moveQuantifiersOutwards :: Node -> Node
moveQuantifiersOutwards node =
    let (quantifiers, expr) = collectQuantifiers node
    in foldr (\(quant, var) acc -> QuantifiedNode quant var acc) expr quantifiers

-- Função auxiliar que coleta quantificadores de uma expressão
collectQuantifiers :: Node -> ([(String, String)], Node)
collectQuantifiers node = case node of
    QuantifiedNode quant var expr ->
        let (quantifiers, innerExpr) = collectQuantifiers expr
        in ((quant, var) : quantifiers, innerExpr)
    -- Aplica recursivamente nos filhos e concatena quantificadores
    BinaryNode op left right ->
        let (leftQuantifiers, leftExpr) = collectQuantifiers left
            (rightQuantifiers, rightExpr) = collectQuantifiers right
        in (leftQuantifiers ++ rightQuantifiers, BinaryNode op leftExpr rightExpr)
    UnaryNode op operand ->
        let (quantifiers, innerExpr) = collectQuantifiers operand
        in (quantifiers, UnaryNode op innerExpr)
    _ -> ([], node)

-- Função que seleciona e aplica transformações para formas normais específicas (CNF ou PNF)
traverseAndReplace :: Node -> String -> Node
traverseAndReplace node normalForm
    | map toLower normalForm `elem` ["fnc", "cnf", "conjunctive"] =
        let node1 = eliminateBiconditionals node
            node2 = eliminateImplications node1
            node3 = moveNegationInwards node2
            node4 = distributeOrOverAnd node3
            node5 = eliminateDoubleNegations node4
            node6 = eliminateUniversalQuantifiers node5
            node7 = eliminateExistentialQuantifiers node6
        in node7
    | map toLower normalForm `elem` ["fnp", "pnf", "prenex"] =
        let node1 = eliminateBiconditionals node
            node2 = eliminateImplications node1
            node3 = moveNegationInwards node2
            node4 = eliminateDoubleNegations node3
            node5 = eliminateUniversalQuantifiers node4
            node6 = eliminateExistentialQuantifiers node5
            node7 = moveQuantifiersOutwards node6
        in node7
    | otherwise = error "Not a valid normal form."


-- Função que converte a árvore de expressão para uma string (formato legível)
toString :: Node -> String
toString node = case node of
    -- Para um nó quantificado, adiciona o quantificador e a variável, seguidos da expressão
    QuantifiedNode quant var expr ->
        quant ++ var ++ " " ++ toString expr
    -- Para um nó binário, formata de acordo com o operador
    BinaryNode op left right ->
        case op of
            "<->" -> "(" ++ toString left ++ " \\leftrightarrow " ++ toString right ++ ")"
            "->"  -> "(" ++ toString left ++ " \\to " ++ toString right ++ ")"
            "v"   -> "(" ++ toString left ++ " \\vee " ++ toString right ++ ")"
            "∃"   -> toString left ++ " \\exists " ++ toString right
            "∀"   -> toString left ++ " \\forall " ++ toString right
            "^"   -> "(" ++ toString left ++ " \\wedge " ++ toString right ++ ")"
            -- Formato padrão para operadores desconhecidos
            _     -> "\\(" ++ toString left ++ " " ++ op ++ " " ++ toString right ++ ")\\"
    -- Para um nó unário "~", adiciona o operador de negação
    UnaryNode "~" operand ->
        let operandStr = toString operand
        in if isBinaryNode operand then "\\(" ++ operandStr ++ ")\\" else "\\neg " ++ operandStr
    -- Para um nó folha, retorna o valor (variável ou constante)
    LeafNode val -> val
    -- Caso padrão, retorna string vazia (não deve ocorrer com nós conhecidos)
    _ -> ""

-- Função auxiliar para verificar se um nó é binário (ajuda a formatar adequadamente no caso de negações)
isBinaryNode :: Node -> Bool
isBinaryNode node = case node of
    BinaryNode _ _ _ -> True
    _ -> False

-- Tipos auxiliares para geração e avaliação da tabela-verdade
type Assignment = Map String Bool

-- Função que avalia o valor lógico de uma expressão para uma dada atribuição de variáveis
evaluate :: Node -> Assignment -> Bool
evaluate node assignment = case node of
    -- Para uma variável, busca seu valor na atribuição
    LeafNode var -> fromMaybe False (Map.lookup var assignment)
    -- Para o operador de negação, inverte o valor lógico do operando
    UnaryNode "~" operand -> not (evaluate operand assignment)
    -- Para operadores binários, avalia os operandos de acordo com o operador
    BinaryNode "^" left right -> evaluate left assignment && evaluate right assignment
    BinaryNode "v" left right -> evaluate left assignment || evaluate right assignment
    BinaryNode "->" left right -> not (evaluate left assignment) || evaluate right assignment
    BinaryNode "<->" left right -> evaluate left assignment == evaluate right assignment
    -- Ignora quantificadores na avaliação para simplificação
    _ -> False

-- Função que gera a tabela-verdade para uma expressão dada e lista de variáveis
generateTruthTable :: Node -> [String] -> [[Bool]]
generateTruthTable node vars = do
    -- Gera todas as combinações de valores booleanos para as variáveis
    values <- replicateM (length vars) [True, False]
    -- Cria uma atribuição de variáveis com os valores gerados
    let assignment = Map.fromList (zip vars values)
        -- Avalia a expressão para a atribuição atual
        result = evaluate node assignment
    -- Retorna a linha da tabela com os valores das variáveis e o resultado da expressão
    return (values ++ [result])

-- Função que analisa a expressão e determina se é uma tautologia, contradição ou contingência
analyzeExpression :: Node -> [String] -> String
analyzeExpression parsedTree vars =
    let truthTable = generateTruthTable parsedTree vars
        results = map last truthTable  -- Extrai os resultados da última coluna (resultado da expressão)
    in if all (== True) results
       then "A expressão é uma Tautologia."
       else if all (== False) results
            then "A expressão é uma Contradição."
            else "A expressão é uma Contingência."

            
-- Passo 1: Converte a expressão para a Forma Normal Conjuntiva (CNF)
-- Reutiliza funções que eliminam bicondicionais e implicações, e movem negações para dentro.
-- A distribuição de disjunções sobre conjunções é aplicada após essas transformações.

-- Função principal para transformar a expressão em CNF
convertToCNF :: Node -> Node
convertToCNF = distributeOrOverAnd . moveNegationInwards . eliminateImplications . eliminateBiconditionals

-- Passo 2: Verifica se uma cláusula é uma cláusula de Horn
isHornClause :: Node -> Bool
isHornClause (BinaryNode "^" left right) = isHornClause left && isHornClause right
isHornClause (BinaryNode "v" left right) =
    let literals = collectLiterals (BinaryNode "v" left right)
    in length (filter isPositiveLiteral literals) <= 1
isHornClause node = isPositiveLiteral node || isNegativeLiteral node

-- Coleta os literais de uma cláusula
collectLiterals :: Node -> [Node]
collectLiterals (BinaryNode "v" left right) = collectLiterals left ++ collectLiterals right
collectLiterals node = [node]

-- Verifica se o literal é positivo
isPositiveLiteral :: Node -> Bool
isPositiveLiteral (LeafNode _) = True
isPositiveLiteral _ = False

-- Verifica se o literal é negativo
isNegativeLiteral :: Node -> Bool
isNegativeLiteral (UnaryNode "~" (LeafNode _)) = True
isNegativeLiteral _ = False

-- Coloca tudo junto: converte uma expressão para a Forma de Horn, se possível
convertToHornForm :: Node -> Maybe Node
convertToHornForm node =
    let cnf = convertToCNF node  -- Reutiliza a função convertToCNF
    in if isHornClause cnf then Just cnf else Nothing

            
-- Função principal para processar expressões
main :: IO ()
main = do
    putStrLn "Digite uma expressão lógica ou 'sair' para encerrar."
    putStrLn "Exemplos de algumas expressões que você pode digitar:"
    putStrLn "(A ^ B) -> (C v D)"
    putStrLn "(A ^ ~B) v (~C ^ D) -> (E v F)"
    putStrLn "(p ^ (q v r)) v (~p ^ ~q)"
    putStrLn "~((p ^ q) v ~(r ^ s))"
    putStrLn "~(((p -> q) -> p) -> p)"
    putStrLn "(p -> q) <-> (p -> r)"
    loop

-- Função que mantém o loop até que o usuário digite 'sair'
loop :: IO ()
loop = do
    putStr "\nDigite sua expressão: "
    input <- getLine
    if input == "sair"
        then putStrLn "Encerrando..."
        else do
            processExpression input
            loop

-- Função para processar a expressão lógica fornecida pelo usuário
processExpression :: String -> IO ()
processExpression expr = do
    putStrLn $ "\nExpressão Original: $$ " ++ expr ++ " $$"
    let expr' = replaceSymbols expr
    case validateExpression expr' of
        Left err -> putStrLn err
        Right validExpr -> do
            let tokens = tokenize validExpr
            case parseExpression tokens of
                Left err -> putStrLn $ "Erro de análise: " ++ err
                Right (parsedTree, _) -> do
                    -- Exibir a árvore original
                    putStrLn "\nÁrvore Sintática Original:"
                    putStrLn $ "$$ " ++ show parsedTree ++ " $$"
                    
                    -- Transformar para CNF
                    let cnfTree = convertToCNF parsedTree
                    putStrLn $ "\nExpressão em CNF: $$ " ++ toString cnfTree ++ " $$"

                    -- Verificar se é uma Cláusula de Horn
                    case convertToHornForm parsedTree of
                        Just hornForm -> do
                            putStrLn "\nA expressão foi convertida para uma Cláusula de Horn:"
                            putStrLn $ "$$ " ++ toString hornForm ++ " $$"
                        Nothing -> putStrLn "\nA expressão não pode ser convertida para uma Cláusula de Horn."

                    -- Análise da expressão e tabela verdade
                    let vars = nub $ collectVars parsedTree
                    putStrLn "\nAnálise da Expressão:"
                    putStrLn $ analyzeExpression parsedTree vars
                    
                    putStrLn "\nTabela Verdade:"
                    let truthTable = generateTruthTable parsedTree vars
                    printTruthTable vars truthTable

-- Função para substituir símbolos especiais
replaceSymbols :: String -> String
replaceSymbols = concatMap replace
  where
    replace '∨' = "v"
    replace '∧' = "^"
    replace '→' = "->"
    replace '↔' = "<->"
    replace '¬' = "~"
    replace c   = [c]

-- Função para validar a expressão
validateExpression :: String -> Either String String
validateExpression expr
    | not (all isValidChar expr) = Left "Erro de validação: A expressão contém caracteres inválidos."
    | not (containsLogicalOperator expr) = Left "Erro de validação: A expressão não contém operadores lógicos."
    | otherwise = Right expr
  where
    isValidChar c = isAlpha c || c `elem` " ()^v~∀∃-><->"
    containsLogicalOperator s = any (`elem` s) "^v~-><->"

-- Coleta variáveis da expressão
collectVars :: Node -> [String]
collectVars node = case node of
    LeafNode var -> [var]
    UnaryNode _ operand -> collectVars operand
    BinaryNode _ left right -> collectVars left ++ collectVars right
    QuantifiedNode _ _ expr -> collectVars expr
    _ -> []

-- Função que imprime a tabela verdade com formatação LaTeX
printTruthTable :: [String] -> [[Bool]] -> IO ()
printTruthTable vars table = do
    let header = "\\begin{array}{" ++ replicate (length vars + 1) 'c' ++ "}"
        separator = "\\hline"
        rows = map formatRow table
        footer = "\\end{array}"
        result = unlines $
            [ "$$"
            , header
            , intercalate " & " vars ++ " & \\text{Resultado} \\\\"
            , separator
            ] ++ rows ++ [footer, "$$"]
    
    putStrLn result
  where
    -- Função auxiliar para formatar cada linha da tabela
    formatRow :: [Bool] -> String
    formatRow row = intercalate " & " (map showBool row) ++ " \\\\"

    -- Função para exibir "1" para True e "0" para False
    showBool :: Bool -> String
    showBool True  = "1"
    showBool False = "0"
