-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_subordinate_clock_le_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T16:28:11.896004+00:00
-- url     : https://prove2.me/submissions/100828a9-756c-485c-9876-5a9a8881bb45

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (N : ℕ)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (N : ℝ≥0∞)).toNNReal)
    (σ : ℕ → Ω → ℝ≥0)
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k ω, (σ k ω : ℝ≥0∞) ≤ ruinTime X x D ω := by
  intro k ω
  calc
    (σ k ω : ℝ≥0∞) ≤ (τ ω : ℝ≥0∞) := by
      exact_mod_cast hσle k ω
    _ = ((min (ruinTime X x D ω) (N : ℝ≥0∞)).toNNReal : ℝ≥0∞) := by
      rw [hτeq ω]
    _ ≤ min (ruinTime X x D ω) (N : ℝ≥0∞) :=
      ENNReal.coe_toNNReal_le_self
    _ ≤ ruinTime X x D ω := min_le_left _ _
