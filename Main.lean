import LeanTry.Boolean
open BoolExpr
def main : IO Unit := do
  IO.println "=== Boolean Expression Simplifier ==="

  -- Test environment
  let env : String → Bool := λ
    | "a" => true
    | "b" => false
    | _ => false

  -- Test expressions
  let testExprs : List (String × BoolExpr) := [
    ("a ∧ a", and (var "a") (var "a")),
    ("a ∧ ¬a", and (var "a") (not (var "a"))),
    ("true ∧ a", and trueE (var "a")),
    ("false ∨ b", or falseE (var "b")),
    ("¬¬a", not (not (var "a"))),
    ("a ∧ (b ∧ false)", and (var "a") (and (var "b") falseE)),
    ("(a ∨ a) ∧ true", and (or (var "a") (var "a")) trueE)
  ]

  for (desc, expr) in testExprs do
    let simplified := simplify expr
    let originalEval := eval env expr
    let simplifiedEval := eval env simplified

    IO.println s!"\nExpression: {desc}"
    IO.println s!"Original:   {expr} (evaluates to: {originalEval})"
    IO.println s!"Simplified: {simplified} (evaluates to: {simplifiedEval})"
    IO.println s!"Equivalent: {originalEval == simplifiedEval}"

  -- Interactive example
  IO.println "\n=== Interactive Example ==="
  let complexExpr := and (or (var "x") (not (var "x"))) (and trueE (var "y"))
  IO.println s!"Complex expression: {complexExpr}"
  IO.println s!"Simplified: {simplify complexExpr}"

  -- Test structural equality
  IO.println "\n=== Structural Equality Tests ==="
  let expr1 := and (var "a") (var "b")
  let expr2 := and (var "a") (var "b")
  let expr3 := and (var "b") (var "a")

  IO.println s!"and a b == and a b: {expr1 == expr2}"  -- true
  IO.println s!"and a b == and b a: {expr1 == expr3}"  -- false (structural, not logical)
