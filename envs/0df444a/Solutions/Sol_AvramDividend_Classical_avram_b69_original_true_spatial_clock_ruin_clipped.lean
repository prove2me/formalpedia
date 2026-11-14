-- Prove2me | solution 1 for AvramDividend.Classical.avram_b69_original_true_spatial_clock_ruin_clipped
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:41:08.432758+00:00
-- url     : https://prove2.me/submissions/73666a03-ff72-4a42-b5c5-9d47d70ad927

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An exact physical upcross-clipped clock never moves beyond the original ruin clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (ρ : Ω → ℝ≥0)
    (hρclip : ∀ ω, ρ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (κ : ℕ → Ω → ℝ≥0)
    (hκexact : ∀ k ω, κ k ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal) :
    ∀ k ω, κ k ω ≤ ρ ω ∧
      (κ k ω : ℝ≥0∞) ≤ ruinTime X x D ω := by
  intro k ω
  have hκle : κ k ω ≤ ρ ω := by
    have hmin := ENNReal.toNNReal_mono
      (show (ρ ω : ℝ≥0∞) ≠ ⊤ by simp)
      (min_le_left (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((k : ℝ) + 1) ω))
    rw [hκexact k ω]
    simpa using hmin
  have hMinFinite :
      min (ruinTime X x D ω) (n : ℝ≥0∞) ≠ ⊤ := by
    exact ne_top_of_le_ne_top (by simp)
      (min_le_right (ruinTime X x D ω) (n : ℝ≥0∞))
  have hρRuin : (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω := by
    have hρE : (ρ ω : ℝ≥0∞) ≤
        ((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0∞) := by
      exact_mod_cast hρclip ω
    calc
      (ρ ω : ℝ≥0∞) ≤
          ((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0∞) := hρE
      _ = min (ruinTime X x D ω) (n : ℝ≥0∞) :=
        ENNReal.coe_toNNReal hMinFinite
      _ ≤ ruinTime X x D ω := min_le_left _ _
  refine ⟨hκle, ?_⟩
  have hκE : (κ k ω : ℝ≥0∞) ≤ (ρ ω : ℝ≥0∞) := by
    exact_mod_cast hκle
  exact hκE.trans hρRuin
