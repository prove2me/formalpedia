-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_original_lower_exit_overshoot_terminal_eventually_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:26:06.362193+00:00
-- url     : https://prove2.me/submissions/86e430b9-43bd-41c3-8d94-0aad2fe09f95

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original stopped right-dividend terminal vanishes after an actual
negative ruin overshoot, with a finite-horizon event for each sample. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (hw_neg : ∀ y < 0, w y = 0)
    (τk : ℕ → Ω → ℝ≥0)
    (Wk Termk : ℕ → Ω → ℝ)
    (hWk : ∀ k ω, Wk k ω =
      if τk k ω = 0 ∨ (τk k ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τk k ω) ω - rightLimit D (τk k ω) ω
      else riskProcess X x D (τk k ω) ω)
    (hTermk : ∀ k ω, Termk k ω =
      Real.exp (-(q * (τk k ω : ℝ))) * w (Wk k ω))
    (hovershoot : ∀ᵐ ω ∂P, ∀ᶠ k in atTop,
      0 < τk k ω ∧
      ruinTime X x D ω ≤ (τk k ω : ℝ≥0∞) ∧
      riskProcess X x D (τk k ω) ω < 0) :
    ∀ᵐ ω ∂P, ∀ᶠ k in atTop, Termk k ω = 0 := by
  filter_upwards [hovershoot] with ω hω
  filter_upwards [hω] with k hk
  rcases hk with ⟨hpos, hruin, hneg⟩
  have hbranch :
      ¬ (τk k ω = 0 ∨ (τk k ω : ℝ≥0∞) < ruinTime X x D ω) := by
    intro h
    rcases h with hz | hbefore
    · exact (ne_of_gt hpos) hz
    · exact (not_lt_of_ge hruin) hbefore
  calc
    Termk k ω =
        Real.exp (-(q * (τk k ω : ℝ))) * w (Wk k ω) := hTermk k ω
    _ = Real.exp (-(q * (τk k ω : ℝ))) *
          w (riskProcess X x D (τk k ω) ω) := by
            rw [hWk k ω, if_neg hbranch]
    _ = 0 := by rw [hw_neg _ hneg]; ring