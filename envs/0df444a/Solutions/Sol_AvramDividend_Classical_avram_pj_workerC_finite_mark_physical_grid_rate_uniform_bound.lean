-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_finite_mark_physical_grid_rate_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:15:04.82747+00:00
-- url     : https://prove2.me/submissions/ee4902ad-e978-4d1b-9351-db0f5a94e89e

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Basic
open MeasureTheory Set Filter Topology
noncomputable section

/-- A genuine bounded original physical grid partitions no more than the
full stopped horizon; its constant finite negative-mark rate budget is
uniform under mesh refinement. -/
theorem solution
    (n m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    (∑ _i ∈ Finset.range m,
      ((n : ℝ) / ((m : ℝ) + 1)) * R) ≤
      (n : ℝ) * R := by
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd : 0 < (m : ℝ) + 1 := by positivity
  have hfrac : ((m : ℝ) / ((m : ℝ) + 1)) ≤ 1 :=
    (div_le_iff₀ hd).2 (by linarith)
  calc
    (m : ℝ) * (((n : ℝ) / ((m : ℝ) + 1)) * R) =
        ((m : ℝ) / ((m : ℝ) + 1)) * ((n : ℝ) * R) := by ring
    _ ≤ 1 * ((n : ℝ) * R) :=
      mul_le_mul_of_nonneg_right hfrac (mul_nonneg hn hR)
    _ = (n : ℝ) * R := by ring
