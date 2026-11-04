-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_positive_ruin_zero_landing_terminal_w0
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:15:53.124809+00:00
-- url     : https://prove2.me/submissions/757e3ac7-97bd-4398-bbd2-67da60e4baef

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- At positive original ruin landing exactly on zero, the discounted terminal retains w(0). -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hW : ∀ ξ, W ξ =
      if τ ξ = 0 ∨ (τ ξ : ℝ≥0∞) < ruinTime X x D ξ
      then x + X.X (τ ξ) ξ - rightLimit D (τ ξ) ξ
      else riskProcess X x D (τ ξ) ξ)
    (w : ℝ → ℝ)
    (hTerm : ∀ ξ, Term ξ =
      Real.exp (-(q * (τ ξ : ℝ))) * w (W ξ))
    (ω : Ω) (hτpos : 0 < τ ω)
    (hτruin : (τ ω : ℝ≥0∞) = ruinTime X x D ω)
    (hLandZero : riskProcess X x D (τ ω) ω = 0) :
    Term ω = Real.exp (-(q * (τ ω : ℝ))) * w 0 := by
  have hnot : ¬ (τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω) := by
    intro h
    rcases h with hz | hlt
    · exact (ne_of_gt hτpos) hz
    · rw [← hτruin] at hlt
      exact (lt_irrefl _) hlt
  have hW0 : W ω = 0 := by
    rw [hW ω, if_neg hnot]
    exact hLandZero
  rw [hTerm ω, hW0]
