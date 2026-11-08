-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux20_finite_mark_product_first_order_remainder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:43:00.008266+00:00
-- url     : https://prove2.me/submissions/7c638a50-6cdf-42b2-915c-e12388e3f491

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators
noncomputable section

/-! A nonidentically weighted finite product has a second-factorial
count error in its first-order linearisation. -/
theorem solution
    {α : Type*} [DecidableEq α] (S : Finset α) (z : α → ℝ)
    (hz : ∀ u ∈ S, 0 ≤ z u ∧ z u ≤ 1) :
    0 ≤ (∏ u ∈ S, z u) - (1 - ∑ u ∈ S, (1 - z u)) ∧
    2 * ((∏ u ∈ S, z u) - (1 - ∑ u ∈ S, (1 - z u))) ≤
      (S.card : ℝ) * ((S.card : ℝ) - 1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hza : 0 ≤ z a ∧ z a ≤ 1 := hz a (Finset.mem_insert_self a S)
    have hzS : ∀ u ∈ S, 0 ≤ z u ∧ z u ≤ 1 := by
      intro u hu
      exact hz u (Finset.mem_insert_of_mem hu)
    obtain ⟨hlo, hhi⟩ := ih hzS
    let D : ℝ := ∑ u ∈ S, (1 - z u)
    let R : ℝ := (∏ u ∈ S, z u) - (1 - D)
    have hdlo : 0 ≤ D := Finset.sum_nonneg (by
      intro u hu
      exact sub_nonneg.mpr (hzS u hu).2)
    have hdhi : D ≤ (S.card : ℝ) := by
      calc
        D ≤ ∑ u ∈ S, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro u hu
          linarith [(hzS u hu).1]
        _ = (S.card : ℝ) := by simp
    have hmullo : 0 ≤ z a * R := mul_nonneg hza.1 hlo
    have hmulhi : z a * R ≤ R := by
      have : 0 ≤ (1 - z a) * R := mul_nonneg (sub_nonneg.mpr hza.2) hlo
      nlinarith
    have hremlo : 0 ≤ (1 - z a) * D :=
      mul_nonneg (sub_nonneg.mpr hza.2) hdlo
    have hremhi : (1 - z a) * D ≤ D := by
      have : 0 ≤ z a * D := mul_nonneg hza.1 hdlo
      nlinarith
    have hnat : (↑(S.card + 1) : ℝ) = (S.card : ℝ) + 1 := by push_cast; ring
    have hkey :
        (z a * (∏ u ∈ S, z u)) -
        (1 - ((1 - z a) + D)) = z a * R + (1 - z a) * D := by
      dsimp [R]
      ring
    simp only [Finset.prod_insert ha, Finset.sum_insert ha,
      Finset.card_insert_of_notMem ha]
    rw [hnat, show (∑ u ∈ S, (1 - z u)) = D from rfl, hkey]
    constructor
    · nlinarith
    · nlinarith
