-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_20_original_capped_ruin_clock_terminal_eq_horizon_terminal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:40:00.630662+00:00
-- url     : https://prove2.me/submissions/7a44811e-2905-43a3-b675-6c3038b2989b

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Stopping at capped ruin preserves exactly the killed horizon terminal. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (ω : Ω) (n : ℕ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
    (if (τ : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (Real.exp (-(q * (τ : ℝ))) *
        w (x + X.X τ ω - rightLimit D τ ω))
    else 0) =
    (if (n : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (Real.exp (-(q * (n : ℝ))) *
        w (x + X.X (n : ℝ≥0) ω - rightLimit D (n : ℝ≥0) ω))
    else 0) := by
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
  have hFinite : min (ruinTime X x D ω) (n : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (min_le_right _ _)
  have hCoe : (τ : ℝ≥0∞) =
      min (ruinTime X x D ω) (n : ℝ≥0∞) := by
    dsimp [τ]
    exact ENNReal.coe_toNNReal hFinite
  have hNatCoe : ((n : ℝ≥0) : ℝ≥0∞) = (n : ℝ≥0∞) := by
    norm_cast
  have hNatReal : ((n : ℝ≥0) : ℝ) = (n : ℝ) := by
    norm_cast
  change (if (τ : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (Real.exp (-(q * (τ : ℝ))) *
        w (x + X.X τ ω - rightLimit D τ ω))
    else 0) =
    (if (n : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (Real.exp (-(q * (n : ℝ))) *
        w (x + X.X (n : ℝ≥0) ω - rightLimit D (n : ℝ≥0) ω))
    else 0)
  by_cases hRu : ruinTime X x D ω ≤ (n : ℝ≥0∞)
  · have hNoLeft : ¬ (τ : ℝ≥0∞) < ruinTime X x D ω := by
      rw [hCoe, min_eq_left hRu]
      exact lt_irrefl _
    have hNoRight : ¬ (n : ℝ≥0∞) < ruinTime X x D ω :=
      not_lt.mpr hRu
    simp only [if_neg hNoLeft, if_neg hNoRight]
  · have hBefore : (n : ℝ≥0∞) < ruinTime X x D ω :=
      lt_of_not_ge hRu
    have hTauEq : τ = (n : ℝ≥0) := by
      apply ENNReal.coe_injective
      rw [hCoe, min_eq_right (le_of_lt hBefore), hNatCoe]
    simpa only [hTauEq, hNatCoe, hNatReal, if_pos hBefore]
