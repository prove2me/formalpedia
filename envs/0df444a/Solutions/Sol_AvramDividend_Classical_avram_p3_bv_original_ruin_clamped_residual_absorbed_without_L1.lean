-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_ruin_clamped_residual_absorbed_without_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:51:39.421197+00:00
-- url     : https://prove2.me/submissions/f62bccfb-9cca-430f-951d-7e122a2afd30

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_random_ruin_clock_residual_nonpositive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- A physical ruin-clamped BV residual is a discardable nonpositive pathwise
term. No integrability of this residual is needed for the HJB expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (τ : Ω → ℝ≥0) (W : ℕ → Ω → ℝ)
    (hW : ∀ ω i, 0 ≤ W i ω)
    (Payoff Correction : Ω → ℝ) (initial : ℝ)
    (hSource : ∀ᵐ ω ∂P,
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
            else 0)
      Payoff ω ≤ initial + Correction ω +
        (∑ i ∈ Finset.range n,
          W i ω * (R (min (u i) (τ ω)) -
            R (min (u (i + 1)) (τ ω))))) :
    ∀ᵐ ω ∂P, Payoff ω ≤ initial + Correction ω := by
  have hR := avram_p3_bv_original_random_ruin_clock_residual_nonpositive
    X hBV u n hGrid τ W hW
  filter_upwards [hR, hSource] with ω hRω hSourceω
  dsimp only at hRω hSourceω
  linarith
