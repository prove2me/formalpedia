-- Prove2me | solution 1 for CircuitComplexity.Schnorr.xorBool_insertAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:01.765974+00:00
-- url     : https://prove2.me/submissions/fc10dd38-d511-45e0-8917-c8ce1fb4c197

module
public import Definitions.Def_LeanPool_CircuitComplexity_XOR
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_CircDesc
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Schnorr
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth



set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Schnorr
namespace CircuitComplexity.Schnorr
theorem _root_.solution {N : Nat} (x : BitString N) (a : Fin (N + 1)) (b : Bool) :
    xorBool (N + 1) (insertAt x a b) = b.xor (xorBool N x) := by
  induction N with
  | zero =>
    have ha : a = 0 := Fin.ext (by omega)
    subst ha; simp [xorBool, insertAt]
  | succ n ih =>
    change (insertAt x a b 0).xor (xorBool (n + 1) (insertAt x a b ∘ Fin.succ)) =
      b.xor ((x 0).xor (xorBool n (x ∘ Fin.succ)))
    by_cases ha : a = 0
    · subst ha
      have h0 : insertAt x 0 b 0 = b := by simp [insertAt]
      have htail : insertAt x 0 b ∘ Fin.succ = x := by
        funext i; simp [insertAt, Fin.succ, Function.comp]
      rw [h0, htail]
      rfl
    · have hpos : 0 < a.val := Nat.pos_of_ne_zero (fun h => ha (Fin.ext h))
      have h0 : insertAt x a b 0 = x 0 := by simp [insertAt]; omega
      rw [h0]
      set a' : Fin (n + 1) := ⟨a.val - 1, by omega⟩
      have htail : insertAt x a b ∘ Fin.succ = insertAt (x ∘ Fin.succ) a' b := by
        funext i; simp only [Function.comp, insertAt, Fin.succ, Fin.val_mk, a']
        split <;> split <;> (try split) <;> (try split)
        all_goals (first | rfl | congr 1; ext; simp_all; omega | omega)
      rw [htail, ih, Bool.xor_left_comm]
end CircuitComplexity.Schnorr
