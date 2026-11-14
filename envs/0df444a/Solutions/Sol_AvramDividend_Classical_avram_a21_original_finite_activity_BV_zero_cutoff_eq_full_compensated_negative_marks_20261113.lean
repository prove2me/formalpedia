-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_finite_activity_BV_zero_cutoff_eq_full_compensated_negative_marks_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T16:51:38.043477+00:00
-- url     : https://prove2.me/submissions/9d6b288b-4b63-4b12-bbe6-411696d78db1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_BV_finite_negative_activity_physical_levy_ito_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The BV original zero-cutoff Gaussian residual is the true compensated small-negative jump limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hBV : X.BoundedVariation)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (Jsmall t ω))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω =
        Jsmall t ω := by
  have hPath :=
    avram_a22_original_BV_finite_negative_activity_physical_levy_ito_exact
      X hX hBV hFinite Jsmall hJ
  filter_upwards [hPath] with ω hω
  intro t
  have hZero :=
    avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff X t ω
  simp only [avram_p4_h_gaussian_intrinsic_truncated_residual] 
  rw [hZero]
  linarith [hω t]
