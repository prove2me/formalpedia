-- Prove2me | solution 1 for Bl.general_b_fact_second_rest.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:13:40.998222+00:00
-- url     : https://prove2.me/submissions/3b33d7a3-2795-43a2-a891-569e898b7e74

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondRest_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u_1 u_2
namespace Bl.general_b_fact_second_rest
private lemma aux {K : Type u_1} [Field K] [NumberField K] (a : K) :
    ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ ((d : K) * a) := by
  have ha : IsAlgebraic ℤ a := IsFractionRing.isAlgebraic_iff ℤ ℚ K |>.mpr (.of_finite ℚ a)
  obtain ⟨d, hd, hint⟩ := ha.exists_integral_multiple
  exact ⟨d, hd, by simpa [zsmul_eq_mul] using hint⟩
end Bl.general_b_fact_second_rest
end

set_option autoImplicit false
universe u_1 u_2
open Bl Bl.general_b_fact_second_rest
namespace Bl.general_b_fact_second_rest
theorem _root_.solution :
  ∀ {K : Type u_1} {V : Type u_2} [inst : Field.{u_1} K] [NumberField.{u_1} K] [NumberField.IsTotallyComplex.{u_1} K]
  [StarRing.{u_1} K] [inst_4 : AddCommGroup.{u_2} V] [inst_5 : Module.{u_1, u_2} K V]
  [inst_6 : Module.{u_1, u_2} (NumberField.RingOfIntegers.{u_1} K) V]
  [IsScalarTower.{u_1, u_1, u_2} (NumberField.RingOfIntegers.{u_1} K) K V]
  (L : Submodule.{u_1, u_2} (NumberField.RingOfIntegers.{u_1} K) V),
  Eq.{u_2 + 1} (Submodule.span.{u_1, u_2} K (SetLike.coe.{u_2, u_2} L)) Top.top.{u_2} →
    ∀ (y : V), Exists.{1} fun (c : Int) ↦ And (Ne.{1} c 0) (Membership.mem.{u_2, u_2} L (HSMul.hSMul.{0, u_2, u_2} c y)) := by
  intro K V _ _ _ _ _ _ _ _ L hL y
  have hy : y ∈ Submodule.span K (L : Set V) := by rw [hL]; exact Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add x z _ _ h1 h2 =>
    obtain ⟨c1, hc1, m1⟩ := h1
    obtain ⟨c2, hc2, m2⟩ := h2
    refine ⟨c1 * c2, mul_ne_zero hc1 hc2, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.toAddSubgroup.zsmul_mem m1 c2
    · rw [mul_smul]; exact L.toAddSubgroup.zsmul_mem m2 c1
  | smul a x _ h =>
    obtain ⟨c, hc, m⟩ := h
    obtain ⟨d, hd, hint⟩ := aux a
    refine ⟨d * c, mul_ne_zero hd hc, ?_⟩
    obtain ⟨r, hr⟩ : ∃ r : NumberField.RingOfIntegers K,
        algebraMap (NumberField.RingOfIntegers K) K r = (d : K) * a := ⟨⟨_, hint⟩, rfl⟩
    have key : (d * c) • (a • x) = r • (c • x) := by
      rw [← algebraMap_smul K r (c • x), hr, ← Int.cast_smul_eq_zsmul K,
        ← Int.cast_smul_eq_zsmul K, smul_smul, smul_smul]
      congr 1
      push_cast
      ring
    rw [key]
    exact L.smul_mem _ m
end Bl.general_b_fact_second_rest
