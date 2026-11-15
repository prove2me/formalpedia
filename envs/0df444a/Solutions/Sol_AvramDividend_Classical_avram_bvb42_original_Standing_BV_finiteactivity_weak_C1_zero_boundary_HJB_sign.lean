-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb42_original_Standing_BV_finiteactivity_weak_C1_zero_boundary_HJB_sign
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:46:40.613613+00:00
-- url     : https://prove2.me/submissions/98cc8aad-8ec6-4744-b3bd-fbd3270b6479
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
import Theorems.Thm_AvramDividend_Classical_avram_bvb45_original_finite_activity_negative_mark_kernel_right_continuous_at_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    X.drift +
      (∫ z in Iio (0 : ℝ), w ((0 : ℝ) + z) - w 0 ∂X.ν) -
      q * w 0 ≤ 0  := by
  have hd : 0 ≤ X.drift := (bv_standing_drift_pos X hStanding hBV).1.le
  have hc : 0 < C.toReal := ENNReal.toReal_pos hC.ne' hFinite
  let y : ℕ → ℝ := fun n => C.toReal / ((n : ℝ) + 2)
  have hreal (n : ℕ) : 0 < y n ∧ y n < C.toReal := by
    dsimp [y]
    have hn : 0 < (n : ℝ) + 2 := by positivity
    constructor
    · exact div_pos hc hn
    · apply (div_lt_iff₀ hn).2
      nlinarith
  have hinside (n : ℕ) : 0 < y n ∧ ENNReal.ofReal (y n) < C := by
    refine ⟨(hreal n).1, ?_⟩
    exact (ENNReal.ofReal_lt_iff_lt_toReal (hreal n).1.le hFinite).2 (hreal n).2
  have hy : Tendsto y atTop (𝓝 (0 : ℝ)) := by
    have h := (tendsto_natCast_atTop_atTop.comp
      (tendsto_add_atTop_nat 2)).const_div_atTop C.toReal
    convert h using 1
    funext n
    simp only [y, Function.comp_apply, Nat.cast_add, Nat.cast_ofNat]
  have hW0 : Tendsto (fun n => w (y n)) atTop (𝓝 (w 0)) := by
    apply (hwCont.continuousWithinAt (Set.mem_Ici.mpr (le_refl 0))).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hy, Filter.Eventually.of_forall
      (fun n => Set.mem_Ici.mpr (hreal n).1.le)⟩
  let K : ℝ → ℝ := fun t =>
    ∫ z in Iio (0 : ℝ), w (t + z) - w t ∂X.ν
  have hKer : Tendsto (fun n => K (y n)) atTop (𝓝 (K 0)) := by
    exact avram_bvb45_original_finite_activity_negative_mark_kernel_right_continuous_at_zero
      X hActivity w C hC hFinite hwCont hwNeg
  have hSrc (n : ℕ) : X.drift + K (y n) - q * w (y n) ≤ 0 := by
    have hG := (hwGen (y n) (hinside n).1 (hinside n).2).2
    have hR := boundedVariation_generator_physical_drift_representation
      X hBV w (y n) (hwGen (y n) (hinside n).1 (hinside n).2).1
    rw [hR] at hG
    have hSlope := hwGrad (y n) (hinside n).1 (hinside n).2
    change X.drift * deriv w (y n) + K (y n) - q * w (y n) ≤ 0 at hG
    nlinarith [mul_nonneg hd (sub_nonneg.mpr hSlope)]
  have hExpr : Tendsto
      (fun n : ℕ => X.drift + K (y n) - q * w (y n))
      atTop (𝓝 (X.drift + K 0 - q * w 0)) := by
    exact (tendsto_const_nhds.add hKer).sub
      (tendsto_const_nhds.mul hW0)
  have hEventually : ∀ᶠ n : ℕ in atTop,
      X.drift + K (y n) - q * w (y n) ∈ Iic (0 : ℝ) :=
    Filter.Eventually.of_forall (fun n => Set.mem_Iic.mpr (hSrc n))
  exact isClosed_Iic.mem_of_tendsto hExpr hEventually
