-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_h_localise_two_interior_reserves_on_common_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:09:03.095744+00:00
-- url     : https://prove2.me/submissions/043c26ef-edd7-491f-9b73-56d95ccfd7f4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Two original interior reserve states admit a common closed positive-cap
band, with the same lower-cutoff hypothesis required by the actual stopped
nonlinear jump compensator. -/
theorem solution
    (C : ℝ≥0∞) (z₁ z₂ : ℝ)
    (h₁ : 0 < z₁ ∧ ENNReal.ofReal z₁ < C)
    (h₂ : 0 < z₂ ∧ ENNReal.ofReal z₂ < C) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ 2 ∧ a ≤ b ∧
      z₁ ∈ Icc a b ∧ z₂ ∈ Icc a b ∧
      Icc (a / 2) b ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
  let m : ℝ := min z₁ z₂
  let b : ℝ := max z₁ z₂
  have hm : 0 < m := by
    dsimp [m]
    exact lt_min h₁.1 h₂.1
  have hbC : ENNReal.ofReal b < C := by
    dsimp [b]
    rcases le_total z₁ z₂ with h | h
    · rw [max_eq_right h]
      exact h₂.2
    · rw [max_eq_left h]
      exact h₁.2
  let a : ℝ := min (m / 2) 1
  have ha : 0 < a := by
    dsimp [a]
    exact lt_min (by linarith) (by norm_num)
  have ha2 : a ≤ 2 := by
    have h := min_le_right (m / 2) (1 : ℝ)
    dsimp [a]
    linarith
  have ham : a ≤ m := by
    have h := min_le_left (m / 2) (1 : ℝ)
    dsimp [a]
    linarith
  have ham1 : a ≤ z₁ := le_trans ham (min_le_left z₁ z₂)
  have ham2 : a ≤ z₂ := le_trans ham (min_le_right z₁ z₂)
  have hzb1 : z₁ ≤ b := le_max_left z₁ z₂
  have hzb2 : z₂ ≤ b := le_max_right z₁ z₂
  refine ⟨a, b, ha, ha2, le_trans ham1 hzb1,
    ⟨ham1, hzb1⟩, ⟨ham2, hzb2⟩, ?_⟩
  intro y hy
  change 0 < y ∧ ENNReal.ofReal y < C
  constructor
  · exact lt_of_lt_of_le (half_pos ha) hy.1
  · exact lt_of_le_of_lt (ENNReal.ofReal_mono hy.2) hbC
