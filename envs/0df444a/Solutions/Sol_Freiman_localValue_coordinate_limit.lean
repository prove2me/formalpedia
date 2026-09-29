-- Prove2me | solution 1 for Freiman.localValue_coordinate_limit
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:21:52.889477+00:00
-- url     : https://prove2.me/submissions/cafb11bc-3c42-4125-bbd7-1c422f19adee

import Theorems.Thm_Freiman_localValue_window_bound
import Theorems.Thm_Freiman_cylinder_bound_tendsto
import Theorems.Thm_Freiman_coordinate_eventual_window

open Freiman Filter

theorem solution (A : ℕ → ℤ → ℕ+) (b : ℤ → ℕ+)
    (h : ∀ i : ℤ, ∀ᶠ n in Filter.atTop, A n i = b i) :
    ∀ i : ℤ, Filter.Tendsto (fun n => localValue (A n) i)
      Filter.atTop (nhds (localValue b i)) := by
  intro i
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨R, hR⟩ := Metric.tendsto_atTop.1 cylinder_bound_tendsto ε hε
  have hsize : 2 / ((Nat.fib (R + 1) : ℝ) ^ 2) < ε := by
    apply lt_of_le_of_lt (le_abs_self _)
    simpa only [Real.dist_eq, sub_zero] using hR R le_rfl
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (coordinate_eventual_window A b h i R)
  refine ⟨N, ?_⟩
  intro n hn
  rw [Real.dist_eq]
  exact (localValue_window_bound (A n) b i R (hN n hn)).trans_lt hsize

