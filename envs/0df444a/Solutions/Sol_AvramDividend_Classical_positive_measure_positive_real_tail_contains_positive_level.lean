-- Prove2me | solution 1 for AvramDividend.Classical.positive_measure_positive_real_tail_contains_positive_level
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:12:50.26289+00:00
-- url     : https://prove2.me/submissions/fbee4d06-e9a4-4a3f-8796-6acafbd1b064

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

/-- Positive mass strictly above zero gives positive mass strictly above
some positive real level, without requiring measurability of the function. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (f : Ω → ℝ)
    (hpos : 0 < μ {ω : Ω | 0 < f ω}) :
    ∃ ε : ℝ, 0 < ε ∧ 0 < μ {ω : Ω | ε < f ω} := by
  by_contra hn
  have hzero : ∀ n : ℕ,
      μ {ω : Ω | 1 / ((n : ℝ) + 1) < f ω} = 0 := by
    intro n
    have hε : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    have hnot :
        ¬ 0 < μ {ω : Ω | 1 / ((n : ℝ) + 1) < f ω} := by
      intro hp
      exact hn ⟨_, hε, hp⟩
    exact le_antisymm (le_of_not_gt hnot) zero_le
  have hcover :
      {ω : Ω | 0 < f ω} ⊆
        ⋃ n : ℕ, {ω : Ω | 1 / ((n : ℝ) + 1) < f ω} := by
    intro ω hω
    change 0 < f ω at hω
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hω
    exact mem_iUnion.mpr ⟨n, hn⟩
  have hbound :
      μ {ω : Ω | 0 < f ω} ≤
        ∑' n : ℕ, μ {ω : Ω | 1 / ((n : ℝ) + 1) < f ω} := by
    exact (measure_mono hcover).trans (measure_iUnion_le _)
  have hsum :
      (∑' n : ℕ, μ {ω : Ω | 1 / ((n : ℝ) + 1) < f ω}) = 0 := by
    simp only [hzero, tsum_zero]
  have hbound_zero : μ {ω : Ω | 0 < f ω} ≤ 0 := by
    calc
      μ {ω : Ω | 0 < f ω} ≤
          ∑' n : ℕ, μ {ω : Ω | 1 / ((n : ℝ) + 1) < f ω} := hbound
      _ = 0 := hsum
  exact (not_lt_of_ge hbound_zero) hpos
