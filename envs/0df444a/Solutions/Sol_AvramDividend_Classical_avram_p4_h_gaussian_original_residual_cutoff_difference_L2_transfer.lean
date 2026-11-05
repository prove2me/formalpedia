-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_h_gaussian_original_residual_cutoff_difference_L2_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:41:34.882526+00:00
-- url     : https://prove2.me/submissions/c953d379-8e87-4885-8ac4-0cd481216ea7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The exact original-source squared L2 cutoff difference of the candidate
continuous residual is the squared compensated small-jump difference.
This transfers future P4-G genuine isometry evidence without source Y. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n m : ℕ) (t : ℝ≥0) :
    (Integrable (fun ω : Ω =>
      (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
       avram_p4_h_gaussian_intrinsic_truncated_residual X m t ω) ^ 2) P ↔
     Integrable (fun ω : Ω =>
      (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
       avram_p4_h_gaussian_intrinsic_small_band_compensated X m t ω) ^ 2) P) ∧
    (∫ ω : Ω,
      (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
       avram_p4_h_gaussian_intrinsic_truncated_residual X m t ω) ^ 2 ∂P) =
    (∫ ω : Ω,
      (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
       avram_p4_h_gaussian_intrinsic_small_band_compensated X m t ω) ^ 2 ∂P) := by
  have hpoint : (fun ω : Ω =>
      (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
       avram_p4_h_gaussian_intrinsic_truncated_residual X m t ω) ^ 2) =
    (fun ω : Ω =>
      (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
       avram_p4_h_gaussian_intrinsic_small_band_compensated X m t ω) ^ 2) := by
    funext ω
    simp only [avram_p4_h_gaussian_intrinsic_truncated_residual]
    ring
  constructor
  · rw [hpoint]
  · simp only [hpoint]
