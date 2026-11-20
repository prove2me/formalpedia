-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_rightshift_subclock_three_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:21:07.215183+00:00
-- url     : https://prove2.me/submissions/16c117b1-88dc-4be1-881c-6028927bf998

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} (τ : Ω → ℝ≥0) (σ : ℕ → Ω → ℝ≥0)
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ (k m : ℕ) (ω : Ω),
      σ k ω ≤
        min (τ ω) (σ k ω + ((1 : ℝ≥0) / ((m : ℝ≥0) + 1))) ∧
      min (τ ω) (σ k ω + ((1 : ℝ≥0) / ((m : ℝ≥0) + 1))) ≤ τ ω ∧
      min (τ ω) (σ k ω + ((1 : ℝ≥0) / ((m : ℝ≥0) + 1))) ≤
        σ k ω + ((1 : ℝ≥0) / ((m : ℝ≥0) + 1)) := by
  intro k m ω
  refine ⟨le_min (hσle k ω) ?_, min_le_left _ _, min_le_right _ _⟩
  exact le_add_of_nonneg_right (by positivity)
