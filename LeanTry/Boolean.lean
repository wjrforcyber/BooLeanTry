/-
Some simple Boolean rules.
-/

inductive BoolExpr : Type
  | var (name : String) : BoolExpr
  | trueE : BoolExpr
  | falseE : BoolExpr
  | not (e : BoolExpr) : BoolExpr
  | and (e1 e2 : BoolExpr) : BoolExpr
  | or (e1 e2 : BoolExpr) : BoolExpr
  deriving Repr -- for eval

namespace BoolExpr

-- BEq instance for structural equality TODO @Jingren: Logic eq?
def beq : BoolExpr → BoolExpr → Bool
  | var n1, var n2 => n1 == n2
  | trueE, trueE => true
  | falseE, falseE => true
  | not e1, not e2 => beq e1 e2
  | and e1 e2, and e3 e4 => beq e1 e3 && beq e2 e4
  | or e1 e2, or e3 e4 => beq e1 e3 && beq e2 e4
  | _, _ => false

instance : BEq BoolExpr := ⟨beq⟩

-- Semantics: evaluation function
def eval (env : String → Bool) : BoolExpr → Bool
  | var name => env name
  | trueE => true
  | falseE => false
  | not e => !(eval env e)
  | and e1 e2 => (eval env e1) && (eval env e2)
  | or e1 e2 => (eval env e1) || (eval env e2)

-- Basic simplification rules with correctness proofs
theorem and_idempotent (e : BoolExpr) (env : String → Bool) :
  (and e e).eval env = e.eval env := by
  simp [eval]

theorem or_idempotent (e : BoolExpr) (env : String → Bool) :
  (or e e).eval env = e.eval env := by
  simp [eval]

theorem and_true (e : BoolExpr) (env : String → Bool) :
  (and e trueE).eval env = e.eval env := by
  simp [eval]

theorem and_false (e : BoolExpr) (env : String → Bool) :
  (and e falseE).eval env = false := by
  simp [eval]

-- Optimized simplification function
def simplify : BoolExpr → BoolExpr
  | and e1 e2 =>
    let e1' := simplify e1
    let e2' := simplify e2
    match e1', e2' with
    | falseE, _ => falseE
    | _, falseE => falseE
    | trueE, e => e
    | e, trueE => e
    | e1'', e2'' =>
      if e1'' == e2'' then e1''  -- idempotence
      else and e1'' e2''
  | or e1 e2 =>
    let e1' := simplify e1
    let e2' := simplify e2
    match e1', e2' with
    | trueE, _ => trueE
    | _, trueE => trueE
    | falseE, e => e
    | e, falseE => e
    | e1'', e2'' =>
      if e1'' == e2'' then e1''  -- idempotence
      else or e1'' e2''
  | not e =>
    match simplify e with
    | trueE => falseE
    | falseE => trueE
    | not e' => e'  -- double negation
    | e' => not e'
  | e => e

-- PP: Pretty printer for BoolExpr. TODO@Jingren Wang: Remove PP to a seperate package
def toString : BoolExpr → String
  | var name => name
  | trueE => "true"
  | falseE => "false"
  | not e => s!"¬({toString e})"
  | and e1 e2 => s!"({toString e1} ∧ {toString e2})"
  | or e1 e2 => s!"({toString e1} ∨ {toString e2})"

instance : ToString BoolExpr := ⟨BoolExpr.toString⟩
#eval (beq trueE trueE)
#eval (beq trueE falseE)

--structurally eq, not logically eq--
#eval (beq (and trueE falseE) (and trueE falseE))
#eval (beq (and falseE trueE) (and trueE falseE))

#check simplify (and trueE falseE)
#eval simplify (and trueE falseE)
end BoolExpr
