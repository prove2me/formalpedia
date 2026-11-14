-- Prove2me | solution 1 for AvramDividend.Classical.avram_a22_original_positive_sigma_intrinsic_limit_true_same_filtration_gaussian_companion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:44:25.270078+00:00
-- url     : https://prove2.me/submissions/5b702d2b-2220-437f-af48-f6af158d3e06
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_zero_nu_intrinsic_gaussian_limit_sameX_companion
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_positive_sigma_nonzero_nu_intrinsic_true_same_filtration_gaussian_companion
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Split the original positive Gaussian source on the genuine original negative jump measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)))
    (hSigma : 0 < X.σ) :
    ∃ Y : SpectrallyNegativeLevy P 𝓕,
      Y.ν = 0 ∧ Y.σ = X.σ ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        R t ω = Y.X t ω - (t : ℝ) * Y.c) := by
  by_cases hNu : X.ν = 0
  · exact avram_a22_original_zero_nu_intrinsic_gaussian_limit_sameX_companion
      X hNu R hR
  · exact avram_a22_original_positive_sigma_nonzero_nu_intrinsic_true_same_filtration_gaussian_companion
      X hX hFinite R hR hSigma hNu
