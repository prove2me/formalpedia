-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_physical_gaussian_limit_rightcont_on_source_conull_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:56:32.986375+00:00
-- url     : https://prove2.me/submissions/217a1813-dd9f-4a95-87cb-ae928af981e4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_allpath_gaussian_cutoff_rightcont_zero_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a24_compact_uniform_real_rates_to_locally_uniform_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a24_rightcont_of_locally_uniform_rightcont_cutoffs_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual original intrinsic Gaussian limit is right-continuous at every time on one source conull event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R : ℝ≥0 → Ω → ℝ)
    (hRate : ∀ᵐ ω ∂P, ∀ K : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ T : ℝ≥0, T ≤ (K : ℝ≥0) →
        |avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
          R T ω| ≤ ε) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun u : ℝ≥0 => R u ω) (Ici t) t := by
  filter_upwards [hRate] with ω hω
  intro t
  have hRight (n : ℕ) :
      ContinuousWithinAt
        (fun u : ℝ≥0 =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X n u ω)
        (Ici t) t :=
    (avram_a24_original_allpath_gaussian_cutoff_rightcont_zero_20261113
      X n ω).1 t
  have hUniform :=
    avram_a24_compact_uniform_real_rates_to_locally_uniform_20261113
      (fun n u => avram_p4_h_gaussian_intrinsic_truncated_residual X n u ω)
      (fun u => R u ω) hω t
  exact avram_a24_rightcont_of_locally_uniform_rightcont_cutoffs_20261113
    (fun n u => avram_p4_h_gaussian_intrinsic_truncated_residual X n u ω)
    (fun u => R u ω) t hRight hUniform
