-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_positive_ruin_terminal_zero_landing_vs_overshoot
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:58:40.752444+00:00
-- url     : https://prove2.me/submissions/3889dbb7-a8ff-47b8-9ee9-e86c526e0d96

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exact positive-ruin terminal: zero landing keeps w(0), negative overshoot kills it. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (ω : Ω) (hpos : 0 < τ ω)
    (hRuin : ruinTime X x D ω ≤ (τ ω : ℝ≥0∞))
    (hNonpos : riskProcess X x D (τ ω) ω ≤ 0) :
    (Term ω = if riskProcess X x D (τ ω) ω = 0
      then Real.exp (-(q * (τ ω : ℝ))) * w 0
      else 0) ∧ 0 ≤ Term ω := by
  have hNotPre :
      ¬ (τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω) := by
    push_neg
    exact ⟨ne_of_gt hpos, hRuin⟩
  have hRuinW : W ω = riskProcess X x D (τ ω) ω := by
    simpa [hNotPre] using hW ω
  have hRuinterm : Term ω =
      Real.exp (-(q * (τ ω : ℝ))) *
        w (riskProcess X x D (τ ω) ω) := by
    rw [hTerm ω, hRuinW]
  have hValue :
      Term ω = if riskProcess X x D (τ ω) ω = 0
        then Real.exp (-(q * (τ ω : ℝ))) * w 0
        else 0 := by
    rw [hRuinterm]
    by_cases hy : riskProcess X x D (τ ω) ω = 0
    · simp [hy]
    · have hneg : riskProcess X x D (τ ω) ω < 0 :=
        lt_of_le_of_ne hNonpos hy
      simp [hy, hw_neg _ hneg]
  refine ⟨hValue, ?_⟩
  rw [hValue]
  split_ifs
  · exact mul_nonneg (le_of_lt (Real.exp_pos _)) hw0
  · exact le_refl 0