-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_positive_cutoff_residual_retained_band_cross_zero_20261113
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:11:18.601906+00:00
-- url     : https://prove2.me/submissions/d0bfbd5c-6cc8-4674-b8f4-c2d7d96d78d0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_residual_retained_zero_time_quadratic_package_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a21_positive_time_positive_cutoff_residual_retained_cross_zero_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The physical positive-cutoff orthogonality reduces to strictly positive horizons. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      let R : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X (n + 1) t ω
      let J : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X (n + 1) t ω
      Integrable (fun ω => R ω * J ω) P ∧
        (∫ ω, R ω * J ω ∂P) = 0 := by
  intro n t
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ t from zero_le) with hzero | hpos
  · rcases hzero with rfl
    exact (avram_a21_original_residual_retained_zero_time_quadratic_package_20261113
      X (n + 1)).2.2
  · exact avram_a21_positive_time_positive_cutoff_residual_retained_cross_zero_20261113
      X hX hFinite n t hpos
