-- Prove2me | solution 1 for Bl.NatMulIsIntegral.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:53.803677+00:00
-- url     : https://prove2.me/submissions/d666b493-1001-4b9e-98c3-fa71bf526722

import Mathlib
import Definitions.Def_Lemmata_NatMulIsIntegral_ExistsNatMulIsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Bl.NatMulIsIntegral
private theorem exists_nat_mul_isIntegral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * c) := by
  obtain ⟨y, hy, hint⟩ := IsAlgebraic.exists_integral_multiple
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c))
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = y.natAbs := ⟨_, rfl⟩
  rcases Int.natAbs_eq y with h | h <;> rw [← hm] at h <;> subst h
  · refine ⟨m, by omega, ?_⟩
    simpa [zsmul_eq_mul] using hint
  · refine ⟨m, by omega, ?_⟩
    have h2 := hint.neg
    simpa [zsmul_eq_mul] using h2
end Bl.NatMulIsIntegral
end

set_option autoImplicit false
open Bl Bl.NatMulIsIntegral
namespace Bl.NatMulIsIntegral
theorem _root_.solution :
  ∀ {E : Type} [inst : Field.{0} E] [NumberField.{0} E] {n : Nat}
  {L : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) (Fin n → E)} {z : Fin n → E},
  Membership.mem.{0, 0} (Submodule.span.{0, 0} E (SetLike.coe.{0, 0} L)) z →
    Exists.{1} fun (N : Nat) ↦ And (LT.lt.{0} 0 N) (Membership.mem.{0, 0} L (HSMul.hSMul.{0, 0, 0} N z)) := by
  intro E _ _ n L z hz
  induction hz using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    have key : (a * b) • (x + y) = b • (a • x) + a • (b • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm b a]
    rw [key]
    exact L.add_mem (nsmul_mem hax b) (nsmul_mem hby a)
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨d, hd, hdi⟩ := exists_nat_mul_isIntegral c
    refine ⟨d * a, Nat.mul_pos hd ha, ?_⟩
    have key : (⟨(d : E) * c, hdi⟩ : NumberField.RingOfIntegers E) • (a • x) = (d * a) • (c • x) := by
      rw [algebra_compatible_smul E (⟨(d : E) * c, hdi⟩ : NumberField.RingOfIntegers E)]
      show ((d : E) * c) • (a • x) = _
      rw [mul_smul, smul_comm c a x, Nat.cast_smul_eq_nsmul E, smul_smul]
    rw [← key]
    exact L.smul_mem _ hax
end Bl.NatMulIsIntegral
