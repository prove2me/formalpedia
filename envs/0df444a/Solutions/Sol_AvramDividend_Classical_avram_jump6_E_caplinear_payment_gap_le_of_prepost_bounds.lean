-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_E_caplinear_payment_gap_le_of_prepost_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:56:06.557748+00:00
-- url     : https://prove2.me/submissions/7321bc00-d7f4-4a11-9327-f1cc378fd567

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Defs.Basic
open MeasureTheory Set Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem solution
    (w V : ℝ → ℝ) (E : ℕ → ℝ) (Y Z : ℕ → ℝ) (m : ℕ)
    (hE : ∀ i, 0 ≤ E i)
    (hY : ∀ i, w (Y i) = V (Y i))
    (hZ : ∀ i, V (Z i) ≤ w (Z i)) :
    (∑ i ∈ Finset.range m, E i * (w (Y i) - w (Z i))) ≤
    (∑ i ∈ Finset.range m, E i * (V (Y i) - V (Z i))) := by
  apply Finset.sum_le_sum
  intro i hi
  have hdiff : w (Y i) - w (Z i) ≤ V (Y i) - V (Z i) := by
    rw [hY i]
    linarith [hZ i]
  exact mul_le_mul_of_nonneg_left hdiff (hE i)
