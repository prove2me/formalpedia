-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux18_finite_mark_product_collision
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:36:47.188818+00:00
-- url     : https://prove2.me/submissions/915d4108-1ca8-4767-954c-567b2fc9a98b

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-! Quadratic collision error for the exponential weight of finite marks. -/
theorem solution
    {α : Type*} [DecidableEq α] (s : Finset α) (q : α → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) :
    0 ≤ (∏ i ∈ s, q i) - (1 - ∑ i ∈ s, (1 - q i)) ∧
    2 * ((∏ i ∈ s, q i) - (1 - ∑ i ∈ s, (1 - q i))) ≤
      (s.card : ℝ) * ((s.card : ℝ) - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      let e : ℝ := (∏ j ∈ s, q j) - (1 - ∑ j ∈ s, (1 - q j))
      let a : ℝ := ∑ j ∈ s, (1 - q j)
      have ha0 : 0 ≤ a := by
        dsimp [a]
        apply Finset.sum_nonneg
        intro j hj
        exact sub_nonneg.mpr (hq1 j)
      have haCard : a ≤ (s.card : ℝ) := by
        dsimp [a]
        calc
          (∑ j ∈ s, (1 - q j)) ≤ ∑ j ∈ s, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro j hj
            linarith [hq0 j]
          _ = s.card := by simp
      have heq :
          (∏ j ∈ insert i s, q j) -
              (1 - ∑ j ∈ insert i s, (1 - q j)) =
            q i * e + (1 - q i) * a := by
        dsimp [e, a]
        simp only [Finset.prod_insert hi, Finset.sum_insert hi]
        ring
      have hscale : q i * e ≤ e := by
        dsimp [e]
        nlinarith [mul_nonneg (sub_nonneg.mpr (hq1 i)) ih.1]
      have haScale : (1 - q i) * a ≤ a := by
        nlinarith [mul_nonneg (hq0 i) ha0]
      constructor
      · rw [heq]
        exact add_nonneg (mul_nonneg (hq0 i) ih.1)
          (mul_nonneg (sub_nonneg.mpr (hq1 i)) ha0)
      · rw [heq]
        simp only [Finset.card_insert_of_notMem hi, Nat.cast_succ]
        dsimp [e] at hscale
        nlinarith [ih.2, hscale, haScale, haCard]
