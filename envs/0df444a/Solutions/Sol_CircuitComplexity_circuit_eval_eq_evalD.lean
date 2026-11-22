-- Prove2me | solution 1 for CircuitComplexity.circuit_eval_eq_evalD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:04.292797+00:00
-- url     : https://prove2.me/submissions/4f2706c2-bd52-4a93-b04f-7bcbf64494ed

module
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_CircDesc
public import Definitions.Def_LeanPool_CircuitComplexity_XOR
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Schnorr
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Bridge
public import Theorems.Thm_CircuitComplexity_wireValue_eq_wireValD
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
public import Theorems.Thm_CircuitComplexity_andOr2_fanIn
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth


section
@[expose] public section
namespace CircuitComplexity
private theorem gate_eval_eq_slot {W W' : Nat} (g : Gate Basis.andOr2 W) (hW : W ≤ W')
    (wireVal : Fin W → Bool) (wireVal' : Fin W' → Bool)
    (hwv : ∀ w : Fin W, wireVal w = wireVal' ⟨w.val, by omega⟩) :
    g.eval wireVal =
      let (isAnd, (w1, w2), (n1, n2)) := encodeGate g hW
      if isAnd then
        (n1.xor (wireVal' w1)) && (n2.xor (wireVal' w2))
      else
        (n1.xor (wireVal' w1)) || (n2.xor (wireVal' w2)) := by
  obtain ⟨op, fanIn, arityOk, inputs, negated⟩ := g
  change fanIn = 2 at arityOk
  subst arityOk
  cases op <;> simp [Gate.eval, Basis.andOr2, encodeGate, AONOp.eval,
    Fin.foldl_succ_last, Fin.foldl_zero, hwv]
end CircuitComplexity
end
end

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
namespace CircuitComplexity
theorem _root_.solution {N G : Nat} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) :
    (fun x => (c.eval x) 0) = evalD (Nat.succ_pos G) (circuitToDesc c) := by
  funext x
  simp only [Circuit.eval, evalD]
  rw [gate_eval_eq_slot (c.outputs 0) (by omega : N + G ≤ N + (G + 1))
    (c.wireValue x) _ (fun w => wireValue_eq_wireValD c x w)]
  conv_rhs => unfold wireValD
  simp only [circuitToDesc, show ¬((⟨N + G.succ - 1 - N, (by omega : N + G.succ - 1 - N < G + 1)⟩ :
    Fin (G + 1)).val < G) from by simp, dite_false]
  have h2 := andOr2_fanIn (c.outputs 0)
  simp only [encodeGate, Fin.val_mk,
    show ((c.outputs 0).inputs ⟨0, by omega⟩).val < N + G.succ - 1 from by
      exact Nat.lt_of_lt_of_le ((c.outputs 0).inputs ⟨0, by omega⟩).isLt (by omega),
    show ((c.outputs 0).inputs ⟨1, by omega⟩).val < N + G.succ - 1 from by
      exact Nat.lt_of_lt_of_le ((c.outputs 0).inputs ⟨1, by omega⟩).isLt (by omega),
    ite_true]
  simp only [show ¬(N + G.succ - 1 < N) from by omega, dite_false]
  rfl
end CircuitComplexity
