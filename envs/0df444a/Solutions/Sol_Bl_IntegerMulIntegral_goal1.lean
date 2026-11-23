-- Prove2me | solution 1 for Bl.IntegerMulIntegral.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:22.157562+00:00
-- url     : https://prove2.me/submissions/b86bd002-126a-44f8-b548-792ae2f83398

import Mathlib
import Definitions.Def_Lemmata_IntegerMulIntegral_IntMulIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Bl.IntegerMulIntegral
private lemma int_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ ((d : E) * a) := by
  have hx : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (.of_finite ℚ a)
  obtain ⟨y, hy, hi⟩ := hx.exists_integral_multiple
  exact ⟨y, hy, by simpa [zsmul_eq_mul] using hi⟩
end Bl.IntegerMulIntegral
end

set_option autoImplicit false
open Bl Bl.IntegerMulIntegral
namespace Bl.IntegerMulIntegral
theorem _root_.solution :
  ∀ {E : Type} [inst : Field.{0} E] [NumberField.{0} E] {n : Nat}
  (L : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) (Fin n → E)) (v : Fin n → E),
  Membership.mem.{0, 0} (Submodule.span.{0, 0} E (SetLike.coe.{0, 0} L)) v →
    Exists.{1} fun (m : Int) ↦ And (Ne.{1} m 0) (Membership.mem.{0, 0} L (HSMul.hSMul.{0, 0, 0} m v)) := by
  intro E _ _ n L v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m1, h1, hm1⟩ := hx
    obtain ⟨m2, h2, hm2⟩ := hy
    refine ⟨m1 * m2, mul_ne_zero h1 h2, ?_⟩
    have e : (m1 * m2) • (x + y) = m2 • (m1 • x) + m1 • (m2 • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm m2 m1]
    rw [e]
    exact L.add_mem (L.toAddSubgroup.zsmul_mem hm1 m2) (L.toAddSubgroup.zsmul_mem hm2 m1)
  | smul a x _ hx =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨d, hd, hi⟩ := int_mul_integral a
    refine ⟨d * m, mul_ne_zero hd hm, ?_⟩
    obtain ⟨r, hr⟩ : ∃ r : NumberField.RingOfIntegers E,
        algebraMap (NumberField.RingOfIntegers E) E r = (d : E) * a := ⟨⟨_, hi⟩, rfl⟩
    have hmem := L.smul_mem r hmx
    convert hmem using 1
    ext i
    change (d * m) • (a * x i) = r • ((m • x) i)
    rw [← algebraMap_smul E r, hr, Pi.smul_apply, smul_eq_mul, zsmul_eq_mul, zsmul_eq_mul, Int.cast_mul]
    ring
end Bl.IntegerMulIntegral
