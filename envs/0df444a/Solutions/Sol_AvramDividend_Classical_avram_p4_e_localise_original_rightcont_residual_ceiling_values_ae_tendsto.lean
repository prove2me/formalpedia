-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_rightcont_residual_ceiling_values_ae_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:31:35.098032+00:00
-- url     : https://prove2.me/submissions/a8be50e1-672d-465a-b1ad-c149584dd5cb

import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.NhdsWithin
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Right-continuous original residual paths transfer upper-clock convergence to almost-sure stopped values. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (f : ℝ≥0 → Ω → ℝ) (u : ℕ → Ω → ℝ≥0)
    (hClock : ∀ ω, Tendsto (fun k => u k ω) atTop (𝓝 (τ ω)))
    (hAbove : ∀ k ω, τ ω ≤ u k ω)
    (hRight : ∀ᵐ ω ∂P, ContinuousWithinAt (fun t => f t ω)
      (Set.Ici (τ ω)) (τ ω)) :
    ∀ᵐ ω ∂P,
      Tendsto (fun k => f (u k ω) ω) atTop (𝓝 (f (τ ω) ω)) := by
  filter_upwards [hRight] with ω hr
  have hu : Tendsto (fun k : ℕ => u k ω) atTop
      (𝓝[Set.Ici (τ ω)] (τ ω)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact hClock ω
    · exact Filter.Eventually.of_forall (fun k => hAbove k ω)
  have ht : Tendsto (fun t : ℝ≥0 => f t ω)
      (𝓝[Set.Ici (τ ω)] (τ ω)) (𝓝 (f (τ ω) ω)) := hr
  exact ht.comp hu
