-- Prove2me | solution 1 for FiniteFields.Dwork.dworkTraceAdditiveCharacter_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T06:41:54.652992+00:00
-- url     : https://prove2.me/submissions/5280d331-987f-4524-a204-c7b9f2806539

import Mathlib
import Definitions.Def_FiniteFields_Dwork_AdditiveCharacter
open scoped BigOperators WithZero
open FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [hpChar : CharP k p] [Finite k]
attribute [local instance] FiniteFields.Dwork.dw4eResiduePrimeAlgebra
attribute [local instance] FiniteFields.Dwork.dw4eDecidableEq
theorem solution :
    dworkTraceAdditiveCharacter k p ≠ 0 := by
  rw [AddChar.ne_zero_iff]
  have htr := (traceForm_nondegenerate (ZMod p) k).1 (1 : k)
  simp_rw [Algebra.traceForm_apply, one_mul] at htr
  have hex : ∃ x : k, Algebra.trace (ZMod p) k x ≠ 0 := by
    by_contra! hzero
    exact one_ne_zero (htr hzero)
  obtain ⟨x, hx⟩ := hex
  refine ⟨x, ?_⟩
  rw [dworkTraceAdditiveCharacter_apply]
  intro hpow
  have hpdiv : p ∣ (Algebra.trace (ZMod p) k x).val :=
    (dworkPrimitiveRoot_isPrimitiveRoot k p).dvd_of_pow_eq_one _ hpow
  have hval : (Algebra.trace (ZMod p) k x).val = 0 := by
    have hlt := ZMod.val_lt (Algebra.trace (ZMod p) k x)
    by_contra hne
    exact (not_le_of_gt hlt) (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hpdiv)
  exact hx ((ZMod.val_eq_zero _).mp hval)
