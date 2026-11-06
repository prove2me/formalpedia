-- Prove2me | solution 2 for AvramDividend.Classical.avram_p4_f4_original_lower_exit_creeping_ae_stopped_terminal_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:31:39.010484+00:00
-- url     : https://prove2.me/submissions/580f609c-4423-4614-9b4b-27e730f45ebe

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_creeping_nonnegative_exit_barrier_discounted_terminal_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Physical creeping band and clock convergence imply terminal convergence a.e. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (τ : Ω → ℝ≥0) (τk : ℕ → Ω → ℝ≥0)
    (Wk Termk : ℕ → Ω → ℝ) (barrier : ℕ → ℝ)
    (hWk : ∀ k ω, Wk k ω =
      if τk k ω = 0 ∨ (τk k ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τk k ω) ω - rightLimit D (τk k ω) ω
      else riskProcess X x D (τk k ω) ω)
    (hTermk : ∀ k ω, Termk k ω =
      Real.exp (-(q * (τk k ω : ℝ))) * w (Wk k ω))
    (hbarrier : Tendsto barrier atTop (𝓝 (0 : ℝ)))
    (hclock : ∀ᵐ ω ∂P,
      Tendsto (fun k => (τk k ω : ℝ)) atTop (𝓝 (τ ω : ℝ)))
    (hbandNN : ∀ᵐ ω ∂P, ∀ k, 0 ≤ Wk k ω)
    (hbandLe : ∀ᵐ ω ∂P, ∀ k, Wk k ω ≤ barrier k) :
    ∀ᵐ ω ∂P, Tendsto (fun k => Termk k ω) atTop
      (𝓝 (Real.exp (-(q * (τ ω : ℝ))) * w 0)) := by
  filter_upwards [hclock, hbandNN, hbandLe] with ω hc hn hl
  have h := avram_p4_f4_creeping_nonnegative_exit_barrier_discounted_terminal_limit
    w hw q (τ ω : ℝ) (fun k => (τk k ω : ℝ))
    (fun k => Wk k ω) barrier hc hbarrier hn hl
  simpa only [hTermk] using h
