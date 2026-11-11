-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise22_original_gaussian_cutoff_exact_second_moment
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T20:53:09.349395+00:00
-- url     : https://prove2.me/submissions/eb95d3a2-cccb-4495-81a2-ffbedd303ac6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_cutoff_gaussian_square_L1
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_cutoff_gaussian_square_expectation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Source-exact assembly of finite-cutoff square integrability and its
original-process quadratic variance identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      Integrable (fun ω =>
        (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) ^ 2) P ∧
      (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) ^ 2 ∂P) =
        (t : ℝ) * X.σ ^ 2 +
          (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν) := by
  have hSq := avram_ja18_original_cutoff_gaussian_square_L1 X hX hFinite
  have hValue :=
    avram_ja18_original_cutoff_gaussian_square_expectation X hX hFinite hSq
  intro n t
  exact ⟨hSq n t, hValue n t⟩
