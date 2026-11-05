-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_h_gaussian_original_residual_L2_cauchy_of_source_smalljump_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:05:57.355192+00:00
-- url     : https://prove2.me/submissions/50f33ce0-c2f3-4e7d-8038-b55c3b28021e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_residual_cutoff_difference_L2_transfer
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Genuine small-band squared-tail estimates on the original filtered
process transfer verbatim to the cutoff residual sequence on that same path.
The source smalljump L2 tail premise remains explicit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (hSmallTail : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ n ≥ N, ∀ m ≥ N,
        Integrable (fun ω : Ω =>
          (avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
           avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2) P ∧
        (∫ ω : Ω,
          (avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
           avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2 ∂P) < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ n ≥ N, ∀ m ≥ N,
        Integrable (fun ω : Ω =>
          (avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
           avram_p4_h_gaussian_intrinsic_truncated_residual X m T ω) ^ 2) P ∧
        (∫ ω : Ω,
          (avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
           avram_p4_h_gaussian_intrinsic_truncated_residual X m T ω) ^ 2 ∂P) < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := hSmallTail ε hε
  refine ⟨N, ?_⟩
  intro n hn m hm
  obtain ⟨hInt, hBound⟩ := hN n hn m hm
  have hTransfer :=
    avram_p4_h_gaussian_original_residual_cutoff_difference_L2_transfer
      X n m T
  refine ⟨hTransfer.1.mpr hInt, ?_⟩
  rw [hTransfer.2]
  exact hBound
