-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_zero13_original_zero_reflected_value_le_HJB_origin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T23:43:23.264976+00:00
-- url     : https://prove2.me/submissions/dd2311dd-7cd3-4510-affc-5ed47bbbe227

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finite_activity_origin_HJB_drift_ceiling
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_zero_reflected_first_jump_payout
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    barrierSupValue X 0 q ≤ ENNReal.ofReal (w 0) := by
  have hRate : 0 < q + (X.ν (Iio (0 : ℝ))).toReal := by
    have hnonneg : 0 ≤ (X.ν (Iio (0 : ℝ))).toReal :=
      ENNReal.toReal_nonneg
    linarith
  have hDrift :
      X.drift ≤ (q + (X.ν (Iio (0 : ℝ))).toReal) * w 0 :=
    avram_bv_correct12_finite_activity_origin_HJB_drift_ceiling
      X hX hBV hFinite q w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad
  have hDrift' :
      X.drift ≤ w 0 * (q + (X.ν (Iio (0 : ℝ))).toReal) := by
    nlinarith [hDrift]
  have hRatio :
      X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal) ≤ w 0 :=
    (div_le_iff₀ hRate).2 hDrift'
  rw [bv_finite_activity_zero_reflected_first_jump_payout X hX q hq
    hBV hFinite]
  exact ENNReal.ofReal_le_ofReal hRatio
