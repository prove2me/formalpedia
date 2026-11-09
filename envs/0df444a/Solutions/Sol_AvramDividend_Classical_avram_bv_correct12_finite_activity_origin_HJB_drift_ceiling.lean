-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_correct12_finite_activity_origin_HJB_drift_ceiling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T21:58:11.318666+00:00
-- url     : https://prove2.me/submissions/4a791650-2ef4-473d-869b-edb748defbd1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finite_activity_positive_cap_HJB_drift_ceiling

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! The actual finite-jump-activity HJB bounds the zero-reserve drift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    X.drift ≤ (q + (X.ν (Iio (0 : ℝ))).toReal) * w 0 := by
  classical
  have hOpen : IsOpen {y : ℝ | ENNReal.ofReal y < C} :=
    isOpen_Iio.preimage ENNReal.continuous_ofReal
  have hCapN : ∀ᶠ y in 𝓝 (0 : ℝ), ENNReal.ofReal y < C :=
    hOpen.mem_nhds (by simpa using hC)
  have hCapR : ∀ᶠ y in 𝓝[>] (0 : ℝ), ENNReal.ofReal y < C :=
    hCapN.filter_mono nhdsWithin_le_nhds
  have hPosR : ∀ᶠ y in 𝓝[>] (0 : ℝ), 0 < y := self_mem_nhdsWithin
  have hRight : Tendsto w (𝓝[>] (0 : ℝ)) (𝓝 (w 0)) :=
    (hw_cont 0 (by simp : (0 : ℝ) ∈ Ici 0)).mono
      (by intro y hy; exact le_of_lt (show (0 : ℝ) < y from hy))
  have hLimit : Tendsto (fun y =>
      (q + (X.ν (Iio (0 : ℝ))).toReal) * w y)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((q + (X.ν (Iio (0 : ℝ))).toReal) * w 0)) :=
    hRight.const_mul _
  apply ge_of_tendsto hLimit
  filter_upwards [hPosR, hCapR] with y hy hyC
  exact avram_bv_correct12_finite_activity_positive_cap_HJB_drift_ceiling
    X hX hBV hFinite q w C hC hw_cont hw0 hw_neg hw_smooth
    hw_gen hw_grad y hy hyC
