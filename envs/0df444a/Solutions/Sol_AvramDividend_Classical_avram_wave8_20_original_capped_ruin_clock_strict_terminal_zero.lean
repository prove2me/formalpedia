-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_20_original_capped_ruin_clock_strict_terminal_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:40:18.439494+00:00
-- url     : https://prove2.me/submissions/eb53b960-3b96-41f5-817f-d6a1980156cb

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Original strict killed terminal at the finite capped ruin clock vanishes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (ω : Ω) (n : ℕ)
    (hRuin : ruinTime X x D ω ≤ (n : ℝ≥0∞)) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
    (if (τ : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (Real.exp (-(q * (τ : ℝ))) *
        w (x + X.X τ ω - rightLimit D τ ω))
    else 0) = 0 := by
  let u : ℝ≥0∞ := min (ruinTime X x D ω) (n : ℝ≥0∞)
  have hu : u ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (min_le_right _ _)
  have hcoe : ((u.toNNReal : ℝ≥0) : ℝ≥0∞) = u :=
    ENNReal.coe_toNNReal hu
  have hMin : u = ruinTime X x D ω := min_eq_left hRuin
  have hNot : ¬ ((u.toNNReal : ℝ≥0) : ℝ≥0∞) <
      ruinTime X x D ω := by
    rw [hcoe, hMin]
    exact lt_irrefl _
  change (if ((u.toNNReal : ℝ≥0) : ℝ≥0∞) <
      ruinTime X x D ω then
      max 0 (Real.exp (-(q * (u.toNNReal : ℝ))) *
        w (x + X.X u.toNNReal ω - rightLimit D u.toNNReal ω))
    else 0) = 0
  simp only [if_neg hNot]
