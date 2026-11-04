-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_original_random_horizon_fourth_moment_mesh_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:16:59.075192+00:00
-- url     : https://prove2.me/submissions/8bde759b-5efc-4385-ae02-bb2dabd56807

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_sigma_fourth_moment_mesh_error_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Source Gaussian fourth-moment mesh coefficient bound on sample-dependent
finite horizons. The analytic bound is useful for stopped integrability,
without asserting any unproved original-process stochastic QV identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ι) (h : ι → Ω → ℝ≥0)
    (τ : Ω → ℝ≥0) (ε : Ω → ℝ)
    (hε : ∀ ω, 0 ≤ ε ω)
    (hmax : ∀ ω, ∀ i ∈ S, (h i ω : ℝ) ≤ ε ω)
    (hT : ∀ ω, (∑ i ∈ S, (h i ω : ℝ)) ≤ (τ ω : ℝ)) :
    ∀ ω, 0 ≤ (2 : ℝ) * X.σ ^ 4 *
        (∑ i ∈ S, (h i ω : ℝ) ^ 2) ∧
      (2 : ℝ) * X.σ ^ 4 * (∑ i ∈ S, (h i ω : ℝ) ^ 2) ≤
        (2 : ℝ) * X.σ ^ 4 * ε ω * (τ ω : ℝ) := by
  intro ω
  exact avram_p4_a_gaussian_original_sigma_fourth_moment_mesh_error_bound
    X S (fun i => h i ω) (τ ω : ℝ) (ε ω)
    (hε ω) (hmax ω) (hT ω)
