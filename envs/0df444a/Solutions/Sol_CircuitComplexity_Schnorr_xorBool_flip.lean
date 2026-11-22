-- Prove2me | solution 1 for CircuitComplexity.Schnorr.xorBool_flip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:10:08.417972+00:00
-- url     : https://prove2.me/submissions/91d1f052-4675-4326-9ce4-3e9cb8109b51

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Definitions.Def_LeanPool_CircuitComplexity_XOR
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth


section
@[expose] public section
namespace CircuitComplexity
namespace Schnorr
private theorem bxor_not_right (a b : Bool) : (a.xor (!b)) = !(a.xor b) := by
  rw [Bool.xor_comm, Bool.not_xor, Bool.xor_comm]
end Schnorr
end CircuitComplexity
end
end

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Schnorr
namespace CircuitComplexity.Schnorr
theorem _root_.solution (N : Nat) (x : BitString N) (a : Fin N) :
    xorBool N (Function.update x a (!x a)) = !xorBool N x := by
  induction N with
  | zero => exact a.elim0
  | succ n ih =>
    change (Function.update x a (!x a) 0).xor
      (xorBool n (Function.update x a (!x a) ∘ Fin.succ)) =
      !((x 0).xor (xorBool n (x ∘ Fin.succ)))
    by_cases ha : a = 0
    · subst ha
      rw [Function.update_self]
      have htail : Function.update x 0 (!x 0) ∘ Fin.succ = x ∘ Fin.succ := by
        funext i; simp_all
      rw [htail, Bool.not_xor]
    · rw [Function.update_of_ne (Ne.symm ha)]
      have hpos : 0 < a.val := Nat.pos_of_ne_zero (fun h => ha (Fin.ext h))
      set a' : Fin n := ⟨a.val - 1, by omega⟩
      have ha_eq : a = Fin.succ a' := by ext; simp [Fin.succ, a']; omega
      have htail : Function.update x a (!x a) ∘ Fin.succ =
          Function.update (x ∘ Fin.succ) a' (!(x ∘ Fin.succ) a') := by
        conv_lhs => rw [ha_eq]
        exact Function.update_comp_eq_of_injective x (Fin.succ_injective n) a' (!x a'.succ)
      rw [htail, ih _ a', bxor_not_right]
end CircuitComplexity.Schnorr
