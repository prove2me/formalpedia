-- Prove2me | solution 2 for AvramDividend.Classical.avram_ja18_original_cutoff_gaussian_square_expectation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T15:53:07.995673+00:00
-- url     : https://prove2.me/submissions/102cca60-c978-4383-bed9-69524f815a25
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja20_integral_square_sum_uncorrelated
import Theorems.Thm_AvramDividend_Classical_avram_ja20_original_cutoff_gaussian_uncorrelated_components

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A genuine original-space orthogonal decomposition gives the cutoff quadratic moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hSq : (∀ (n : ℕ) (t : ℝ≥0), Integrable
      (fun ω => (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) ^ 2) P)) :
    ∀ (n : ℕ) (t : ℝ≥0),
      (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) ^ 2 ∂P) =
        (t : ℝ) * X.σ ^ 2 +
          (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν) := by
  intro n t
  obtain ⟨G, J, heq, hGsq, hJsq, hGJ, hcross, hGa, hJb⟩ :=
    avram_ja20_original_cutoff_gaussian_uncorrelated_components X hX hFinite n t
  have hsum := avram_ja20_integral_square_sum_uncorrelated
    P G J ((t : ℝ) * X.σ ^ 2)
    ((t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν))
    hGsq hJsq hGJ hcross hGa hJb
  have hcongr :
      (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) ^ 2 ∂P) =
        (∫ ω, (G ω + J ω) ^ 2 ∂P) := by
    apply integral_congr_ae
    filter_upwards [heq] with ω hω
    rw [hω]
  exact hcongr.trans hsum
