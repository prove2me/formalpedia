-- Prove2me | solution 2 for AvramDividend.Classical.avram_ja19_same_filtration_zero_nu_from_intrinsic_gaussian_limit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:22:10.87219+00:00
-- url     : https://prove2.me/submissions/76012071-2336-45f3-902b-e5c41ead784e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_sigma_zero_intrinsic_limit_zero_noise_same_filtration_companion
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_zero_nu_intrinsic_gaussian_limit_sameX_companion
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_positive_sigma_nonzero_nu_intrinsic_true_same_filtration_gaussian_companion
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
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω))) :
    ∃ Y : SpectrallyNegativeLevy P 𝓕,
      Y.ν = 0 ∧ Y.σ = X.σ ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        R t ω = Y.X t ω - (t : ℝ) * Y.c) := by
  by_cases hSigmaZero : X.σ = 0
  · exact
      avram_a22_original_sigma_zero_intrinsic_limit_zero_noise_same_filtration_companion
        X hX hFinite R hR hSigmaZero
  · by_cases hNu : X.ν = 0
    · exact
        avram_a22_original_zero_nu_intrinsic_gaussian_limit_sameX_companion
          X hNu R hR
    · have hSigmaPos : 0 < X.σ :=
        lt_of_le_of_ne X.σ_nonneg (Ne.symm hSigmaZero)
      exact
        avram_a22_original_positive_sigma_nonzero_nu_intrinsic_true_same_filtration_gaussian_companion
          X hX hFinite R hR hSigmaPos hNu
