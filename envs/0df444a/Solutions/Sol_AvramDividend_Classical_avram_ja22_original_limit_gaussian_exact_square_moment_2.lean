-- Prove2me | solution 2 for AvramDividend.Classical.avram_ja22_original_limit_gaussian_exact_square_moment
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:45:53.095057+00:00
-- url     : https://prove2.me/submissions/ebd55e47-1c14-4c8f-b4b4-10cab1963b60
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
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

/-- The exact original Gaussian second moment is assembled from the initial time and positive-time results. -/
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
  by_cases ht : t = 0
  · subst t
    simpa using
      avram_a21_original_limit_gaussian_zero_time_square_moment_20261113
        X hX hFinite R hR
  · have htpos : (0 : ℝ≥0) < t := by
      exact lt_of_le_of_ne (bot_le : (0 : ℝ≥0) ≤ t) (Ne.symm ht)
    exact
      avram_a21_original_limit_gaussian_positive_time_square_moment_20261113
        X hX hFinite R hR t htpos
