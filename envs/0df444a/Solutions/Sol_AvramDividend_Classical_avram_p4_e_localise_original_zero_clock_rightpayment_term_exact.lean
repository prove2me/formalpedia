-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_zero_clock_rightpayment_term_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:14:26.960707+00:00
-- url     : https://prove2.me/submissions/8bef0cbe-5514-439f-af1c-01164feb3b78

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At the original stopped clock zero, W and the discounted terminal
    retain the actual time-zero right-dividend payment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (q : ℝ) (w : ℝ → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    ∀ ω, τ ω = 0 →
      W ω = x - rightLimit D 0 ω ∧
      Term ω = w (x - rightLimit D 0 ω) := by
  intro ω hZero
  have hWZero : W ω = x - rightLimit D 0 ω := by
    rw [hW ω, if_pos (Or.inl hZero), hZero]
    simp [X.X_zero ω]
  refine ⟨hWZero, ?_⟩
  rw [hTerm ω, hZero, hWZero]
  simp
