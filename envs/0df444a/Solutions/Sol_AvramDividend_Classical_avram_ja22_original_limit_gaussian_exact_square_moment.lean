-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja22_original_limit_gaussian_exact_square_moment
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:22:39.939898+00:00
-- url     : https://prove2.me/submissions/e027d702-d530-409b-aa0f-cbb91e45fdaf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_limit_gaussian_zero_time_square_moment_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_limit_gaussian_positive_time_square_moment_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The physical Gaussian-limit second moment follows from zero and positive horizons. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω))) :
    ∀ t : ℝ≥0,
      Integrable (fun ω => (R t ω) ^ 2) P ∧
      (∫ ω, (R t ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2 := by
  intro t
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ t from zero_le) with hz | ht
  · rcases hz with rfl
    have h := avram_a21_original_limit_gaussian_zero_time_square_moment_20261113
      X hX hFinite R hR
    simpa using h
  · exact avram_a21_original_limit_gaussian_positive_time_square_moment_20261113
      X hX hFinite R hR t ht
