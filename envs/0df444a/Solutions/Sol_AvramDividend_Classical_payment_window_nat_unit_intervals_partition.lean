-- Prove2me | solution 1 for AvramDividend.Classical.payment_window_nat_unit_intervals_partition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T19:52:45.582991+00:00
-- url     : https://prove2.me/submissions/4c5e1fdf-2a21-4e44-adf9-fbf045b558cd

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (σ : ℝ≥0∞) (T : ℝ) :
    (∀ k : ℕ, MeasurableSet
      ((AvramDividend.Classical.paymentTimes σ ∩ Iic T) ∩ Ico (k : ℝ) ((k : ℝ) + 1))) ∧
    Pairwise (Function.onFun Disjoint
      (fun k : ℕ => (AvramDividend.Classical.paymentTimes σ ∩ Iic T) ∩
        Ico (k : ℝ) ((k : ℝ) + 1))) ∧
    (⋃ k : ℕ, (AvramDividend.Classical.paymentTimes σ ∩ Iic T) ∩
      Ico (k : ℝ) ((k : ℝ) + 1)) =
      AvramDividend.Classical.paymentTimes σ ∩ Iic T := by
  refine ⟨fun k => ?_, ?_, ?_⟩
  · exact ((AvramDividend.Classical.paymentTimes_measurable σ).inter measurableSet_Iic).inter
      measurableSet_Ico
  · intro i j hij
    refine Disjoint.mono inf_le_right inf_le_right ?_
    rw [Set.disjoint_left]
    intro x hi hj
    apply hij
    have h1 : ⌊x⌋₊ = i := Nat.floor_eq_on_Ico i x hi
    have h2 : ⌊x⌋₊ = j := Nat.floor_eq_on_Ico j x hj
    rw [← h1, ← h2]
  · ext x
    simp only [mem_iUnion, mem_inter_iff]
    constructor
    · rintro ⟨k, h, -⟩; exact h
    · intro h
      have hx : 0 ≤ x := h.1.1
      exact ⟨⌊x⌋₊, h, Nat.floor_le hx, Nat.lt_floor_add_one x⟩
