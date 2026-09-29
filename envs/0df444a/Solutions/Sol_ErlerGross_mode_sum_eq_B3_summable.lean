-- Prove2me | solution 1 for ErlerGross.mode_sum_eq_B3_summable
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T12:18:05.077748+00:00
-- url     : https://prove2.me/submissions/e1e316bb-2938-46ee-9da6-792f2e7f6a5a

import Mathlib
import Definitions.Def_ErlerGross_defs
import Theorems.Thm_ErlerGross_B3_cubic_reciprocal_series_closed_form

open Real Filter Topology MeasureTheory ErlerGross

theorem solution :
    Summable (fun n : ℕ => ErlerGross.b3Term (n + 1)) := by
  have h := ErlerGross.B3_cubic_reciprocal_series_closed_form.mul_left (-1 / 2)
  have h' : HasSum (fun n : ℕ => ErlerGross.b3Term (n + 1))
      ((-1 / 2) * Real.log (27 / 16)) := by
    apply h.congr_fun
    intro n
    rw [ErlerGross.b3Term]
    push_cast
    have h1 : (0 : Real) < 2 * (n : Real) + 1 := by positivity
    have h2 : (0 : Real) < 3 * (n : Real) + 1 := by positivity
    have h3 : (0 : Real) < 3 * (n : Real) + 2 := by positivity
    have h4 : (0 : Real) < 1 + (n : Real) * 2 := by positivity
    have h5 : (0 : Real) < 2 + (n : Real) * 3 := by positivity
    have h6 : (0 : Real) < 2 + (n : Real) * 6 := by positivity
    have h7 : (0 : Real) < 2 * ((n : Real) + 1) - 1 := by
      have hn : (0 : Real) <= (n : Real) := by positivity
      nlinarith
    have h8 : (0 : Real) < ((n : Real) + 1) * 3 - 1 := by
      have hn : (0 : Real) <= (n : Real) := by positivity
      nlinarith
    have h9 : (0 : Real) < 2 * ((n : Real) + 1) * 3 - 4 := by
      have hn : (0 : Real) <= (n : Real) := by positivity
      nlinarith
    field_simp [ne_of_gt h1, ne_of_gt h2, ne_of_gt h3, ne_of_gt h4, ne_of_gt h5,
      ne_of_gt h6, ne_of_gt h7, ne_of_gt h8, ne_of_gt h9]
    ring
  exact h'.summable
