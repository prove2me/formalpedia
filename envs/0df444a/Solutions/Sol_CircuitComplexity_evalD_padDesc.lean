-- Prove2me | solution 1 for CircuitComplexity.evalD_padDesc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:12.091548+00:00
-- url     : https://prove2.me/submissions/d214d6a0-d207-46e6-a746-ebaaef479f22

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
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth


section
@[expose] public section
namespace CircuitComplexity
private theorem wireValD_padDesc_lt {N s s' : Nat} (d : CircDesc N s) (hs : 0 < s)
    (h : s ≤ s') (x : BitString N) (w : Fin (N + s')) (hw : w.val < N + s) :
    wireValD (padDesc d s' hs h) x w =
      wireValD d x ⟨w.val, hw⟩ := by
  by_cases hwN : w.val < N
  · simp [wireValD, hwN]
  · push Not at hwN
    have hi : w.val - N < s := by omega
    conv_lhs => unfold wireValD
    simp only [show ¬(w.val < N) from by omega, dite_false]
    conv_rhs => unfold wireValD
    simp only [show ¬(w.val < N) from by omega, dite_false]
    simp only [padDesc, show (w.val - N) < s from hi, dite_true]
    have hw1 : (d ⟨↑w - N, hi⟩).2.1.1.val < N + s := (d ⟨↑w - N, hi⟩).2.1.1.isLt
    have hw2 : (d ⟨↑w - N, hi⟩).2.1.2.val < N + s := (d ⟨↑w - N, hi⟩).2.1.2.isLt
    congr 1 <;> (congr 1 <;> (congr 1; split_ifs with hlt <;> (
      first
      | exact wireValD_padDesc_lt d hs h x _ (by first | exact hw1 | exact hw2)
      | rfl)))
  termination_by w.val
private theorem wireValD_padDesc_ge {N s s' : Nat} (d : CircDesc N s) (hs : 0 < s)
    (h : s ≤ s') (x : BitString N) (w : Fin (N + s')) (hw : N + s ≤ w.val) :
    wireValD (padDesc d s' hs h) x w =
      wireValD d x ⟨N + s - 1, by omega⟩ := by
  conv_lhs => unfold wireValD
  simp only [show ¬(w.val < N) from by omega, dite_false]
  simp only [padDesc, show ¬(w.val - N < s) from by omega, dite_false]
  simp only [Bool.false_xor, Bool.or_self]
  simp only [show (N + s - 1 : Nat) < w.val from by omega, ↓reduceIte]
  have hlt : N + s - 1 < N + s := by omega
  exact wireValD_padDesc_lt d hs h x ⟨N + s - 1, by omega⟩ hlt
end CircuitComplexity
end
end

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
namespace CircuitComplexity
theorem _root_.solution {N s s' : Nat} (d : CircDesc N s) (hs : 0 < s)
    (h : s ≤ s') (hs' : 0 < s') :
    evalD hs' (padDesc d s' hs h) = evalD hs d := by
  funext x
  simp only [evalD]
  by_cases hsle : N + s ≤ N + s' - 1
  · rw [wireValD_padDesc_ge d hs h x ⟨N + s' - 1, by omega⟩ (by omega)]
  · push Not at hsle
    have : s = s' := by omega
    subst this
    exact wireValD_padDesc_lt d hs h x ⟨N + s - 1, by omega⟩ (by omega)
end CircuitComplexity
