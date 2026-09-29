-- Prove2me | solution 1 for Freiman.perron_local_difference_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:21:39.389908+00:00
-- url     : https://prove2.me/submissions/3849c236-546a-4c49-918f-83824e64ff11

import Theorems.Thm_Freiman_perron_local_difference_bound
import Theorems.Thm_Freiman_cylinder_bound_tendsto
import Mathlib.Tactic.Linarith

open Freiman
set_option autoImplicit false

theorem solution (a : ℤ → ℕ+) :
    Filter.Tendsto
      (fun n : ℕ => perronValue (fun k : ℕ => a (k : ℤ)) n - localValue a (n : ℤ))
      Filter.atTop (nhds 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp cylinder_bound_tendsto ε hε
  refine ⟨N, ?_⟩
  intro n hn
  have hh := hN n hn
  rw [Real.dist_eq, sub_zero] at hh ⊢
  have hbound := perron_local_difference_bound a n
  have hnonneg : 0 ≤ 1 / ((Nat.fib (n + 1) : ℝ) ^ 2) := by positivity
  have hlarge : 1 / ((Nat.fib (n + 1) : ℝ) ^ 2) ≤ 2 / ((Nat.fib (n + 1) : ℝ) ^ 2) := by
    exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _)
  exact lt_of_le_of_lt (hbound.trans hlarge) (abs_lt.mp hh).2
