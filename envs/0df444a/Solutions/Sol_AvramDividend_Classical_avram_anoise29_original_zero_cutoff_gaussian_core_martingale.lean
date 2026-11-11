-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise29_original_zero_cutoff_gaussian_core_martingale
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T20:02:45.10837+00:00
-- url     : https://prove2.me/submissions/5d86529b-c06a-4fbb-a105-829029969525
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja18_zero_cutoff_fixed_time_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ja18_zero_cutoff_conditional_increment_centred
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Reassemble the exact original-filtration zero-cutoff L1 and centring obligations. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    (∀ t : ℝ≥0, Integrable
      (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) P) ∧
    (∀ s t : ℝ≥0, s ≤ t → ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont s) P
        (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) ω =
      avram_p4_h_gaussian_intrinsic_truncated_residual X 0 s ω) := by
  have hInt := avram_ja18_zero_cutoff_fixed_time_integrable X hX hFinite
  exact ⟨hInt, avram_ja18_zero_cutoff_conditional_increment_centred X hX hFinite hInt⟩
