-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_ceiling_mesh_residual_ae_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:43:32.259056+00:00
-- url     : https://prove2.me/submissions/feb63f0e-e3e5-4660-b90a-f21a37853535

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_grid_clock_squeeze_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_rightcont_residual_ceiling_values_ae_tendsto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original ceiling-grid mesh bounds and right-continuous residual paths yield stopped-value a.s. convergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (e : ℕ → ℕ → ℝ≥0) (K : ℕ → Ω → ℕ)
    (δ : ℕ → ℝ≥0) (hδ : Tendsto δ atTop (𝓝 0))
    (hBounds : ∀ k ω, τ ω ≤ e k (K k ω) ∧
      e k (K k ω) ≤ τ ω + δ k)
    (f : ℝ≥0 → Ω → ℝ)
    (hRight : ∀ᵐ ω ∂P, ContinuousWithinAt (fun t => f t ω)
      (Set.Ici (τ ω)) (τ ω)) :
    ∀ᵐ ω ∂P, Tendsto (fun k => f (e k (K k ω)) ω)
      atTop (𝓝 (f (τ ω) ω)) := by
  have hLower : ∀ k ω, τ ω ≤ e k (K k ω) :=
    fun k ω => (hBounds k ω).1
  have hUpper : ∀ k ω, e k (K k ω) ≤ τ ω + δ k :=
    fun k ω => (hBounds k ω).2
  have hClock := avram_p4_e_localise_original_ruin_grid_clock_squeeze_tendsto
    X x D n τ hτeq e K δ hδ hLower hUpper
  exact avram_p4_e_localise_original_rightcont_residual_ceiling_values_ae_tendsto
    X x D n τ hτeq f (fun k ω => e k (K k ω)) hClock hLower hRight
