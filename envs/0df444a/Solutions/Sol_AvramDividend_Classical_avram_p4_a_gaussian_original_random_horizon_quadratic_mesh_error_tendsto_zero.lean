-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_original_random_horizon_quadratic_mesh_error_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:15:24.912959+00:00
-- url     : https://prove2.me/submissions/e3a7aea5-1da2-49a2-a353-bd2761217f23

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_sigma_quadratic_mesh_error_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Apply the source Gaussian quadratic-mesh error estimate pathwise when both
the mesh and its finite localising horizon depend on the original sample.
This is an analytic coefficient limit, not a stochastic QV assertion. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : ℕ → Finset ι) (h : ℕ → ι → Ω → ℝ≥0)
    (τ : Ω → ℝ≥0) (ε : ℕ → Ω → ℝ)
    (hε : ∀ ω n, 0 ≤ ε n ω)
    (hmax : ∀ ω n, ∀ i ∈ S n, (h n i ω : ℝ) ≤ ε n ω)
    (hT : ∀ ω n, (∑ i ∈ S n, (h n i ω : ℝ)) ≤ (τ ω : ℝ))
    (hεzero : ∀ ω, Tendsto (fun n => ε n ω) atTop (nhds 0)) :
    ∀ ω, Tendsto
      (fun n => (2 : ℝ) * X.σ ^ 4 *
        (∑ i ∈ S n, (h n i ω : ℝ) ^ 2)) atTop (nhds 0) := by
  intro ω
  exact avram_p4_a_gaussian_original_sigma_quadratic_mesh_error_tendsto_zero
    X S (fun n i => h n i ω) (τ ω : ℝ) (fun n => ε n ω)
    (hε ω) (hmax ω) (hT ω) (hεzero ω)
