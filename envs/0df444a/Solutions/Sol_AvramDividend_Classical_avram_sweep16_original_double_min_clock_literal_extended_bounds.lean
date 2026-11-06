-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_double_min_clock_literal_extended_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:22:22.950674+00:00
-- url     : https://prove2.me/submissions/4e31c265-e5af-4533-9986-6f45e461329c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-! Physical double-min localisation stays finite, below ruin, below n,
    and its NNReal coercion is literally the same extended clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ) (S : ℕ → Ω → ℝ≥0∞) :
    ∀ k ω,
      (((min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal :
        ℝ≥0∞) = min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)) ∧
      (((min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal :
        ℝ≥0∞) ≤ ruinTime X x D ω) ∧
      (((min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal :
        ℝ≥0∞) ≤ (n : ℝ≥0∞)) := by
  intro k ω
  let a : ℝ≥0∞ := min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)
  have ha_n : a ≤ (n : ℝ≥0∞) :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hfin : a ≠ ⊤ := ne_top_of_le_ne_top (by simp) ha_n
  have heq : (a.toNNReal : ℝ≥0∞) = a := ENNReal.coe_toNNReal hfin
  refine ⟨heq, ?_, ?_⟩
  · rw [heq]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  · rw [heq]
    exact ha_n
