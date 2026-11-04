-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_ruin_grid_clock_squeeze_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:31:27.11971+00:00
-- url     : https://prove2.me/submissions/47a86804-7a96-4469-a3f8-ca791672e3de

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original ruin-truncated stopped time is the limit of upper ceiling clocks with vanishing mesh error. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (e : ℕ → ℕ → ℝ≥0) (K : ℕ → Ω → ℕ)
    (δ : ℕ → ℝ≥0) (hδ : Tendsto δ atTop (𝓝 0))
    (hLower : ∀ k ω, τ ω ≤ e k (K k ω))
    (hUpper : ∀ k ω, e k (K k ω) ≤ τ ω + δ k) :
    ∀ ω, Tendsto (fun k => e k (K k ω)) atTop (𝓝 (τ ω)) := by
  intro ω
  have hhi : Tendsto (fun k : ℕ => τ ω + δ k) atTop (𝓝 (τ ω)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add hδ :
        Tendsto (fun k : ℕ => τ ω + δ k) atTop (𝓝 (τ ω + 0)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hhi
    (fun k => hLower k ω)
    (fun k => hUpper k ω)
