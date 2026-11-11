-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_rightcontinuous_clock_composition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T21:27:51.532944+00:00
-- url     : https://prove2.me/submissions/235e2924-4ee3-400c-b80d-4201b11518a0

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- Right-continuous original path evaluation commutes with a
sequence of rounding-up clocks that converges to the physical clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (J : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0)
    (ρ : ℕ → Ω → ℝ≥0)
    (hRight : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun u : ℝ≥0 => J u ω) (Set.Ici t) t)
    (hCeil : ∀ k ω, τ ω ≤ ρ k ω)
    (hConv : ∀ ω, Tendsto (fun k => ρ k ω) atTop (𝓝 (τ ω))) :
    ∀ᵐ ω ∂P, Tendsto (fun k => J (ρ k ω) ω) atTop (𝓝 (J (τ ω) ω)) := by
  filter_upwards [hRight] with ω hω
  have hWithin :
      Tendsto (fun k => ρ k ω) atTop (𝓝[Set.Ici (τ ω)] (τ ω)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact hConv ω
    · filter_upwards [] with k
      exact hCeil k ω
  have hcont : Tendsto (fun u : ℝ≥0 => J u ω)
      (𝓝[Set.Ici (τ ω)] (τ ω)) (𝓝 (J (τ ω) ω)) := hω (τ ω)
  exact hcont.comp hWithin
