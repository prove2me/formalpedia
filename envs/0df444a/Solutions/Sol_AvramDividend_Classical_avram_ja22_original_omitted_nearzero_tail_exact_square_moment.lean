-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja22_original_omitted_nearzero_tail_exact_square_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:10:30.46084+00:00
-- url     : https://prove2.me/submissions/6eb5a45a-1b01-4a95-a56a-0f6360720287

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja22_original_finite_cutoff_strip_exact_square_moment
import Theorems.Thm_AvramDividend_Classical_avram_ja22_original_tail_variance_from_finite_strip_isometry
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
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω))) :
    ∀ (n : ℕ) (t : ℝ≥0),
      Integrable (fun ω =>
        (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω) ^ 2) P ∧
      (∫ ω,
        (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω) ^ 2 ∂P) =
        (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0,
          z ^ 2 ∂X.ν) := by
  exact avram_ja22_original_tail_variance_from_finite_strip_isometry
    X hX hFinite R hR
    (avram_ja22_original_finite_cutoff_strip_exact_square_moment X hX hFinite)
