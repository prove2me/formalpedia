-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_surviving_finite_horizon_rightpayment_terminal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:15:00.046286+00:00
-- url     : https://prove2.me/submissions/f7dac0d1-9b36-404d-a528-e27520abf99e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On exact original finite-horizon survival, both source terminal
    variables use the post-rightpayment finite-horizon reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (W Term : Ω → ℝ) (q : ℝ) (w : ℝ → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    ∀ ω, (n : ℝ≥0∞) < ruinTime X x D ω →
      τ ω = (n : ℝ≥0) ∧
      W ω = x + X.X (n : ℝ≥0) ω - rightLimit D (n : ℝ≥0) ω ∧
      Term ω = Real.exp (-(q * (n : ℝ))) *
        w (x + X.X (n : ℝ≥0) ω - rightLimit D (n : ℝ≥0) ω) := by
  intro ω hSurvive
  have hτn : τ ω = (n : ℝ≥0) := by
    rw [hτeq ω, min_eq_right (le_of_lt hSurvive)]
    simp
  have hStrict : (τ ω : ℝ≥0∞) < ruinTime X x D ω := by
    simpa only [hτn, ENNReal.coe_natCast] using hSurvive
  have hBranch : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω :=
    Or.inr hStrict
  have hWn : W ω =
      x + X.X (n : ℝ≥0) ω - rightLimit D (n : ℝ≥0) ω := by
    rw [hW ω, if_pos hBranch, hτn]
  refine ⟨hτn, hWn, ?_⟩
  rw [hTerm ω, hτn, hWn]
  rfl
