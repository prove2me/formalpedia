-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_abovecap_m2_missing_parentheses_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:02:56.595361+00:00
-- url     : https://prove2.me/submissions/9c674e41-4210-43f2-9f74-37ed5069d7cc

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.NormNum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped BigOperators
noncomputable section

theorem solution :
    let w : ℝ → ℝ := fun y =>
      if y < 0 then 0 else if y ≤ 1 then y else 2 - y
    let V : ℝ → ℝ := fun y =>
      if y ≤ 1 then w y else w 1 + (y - 1)
    (∑ _i ∈ Finset.range (2 : ℕ),
      V (1 + 1 / (2 : ℝ)) - w (1 + 1 / (2 : ℝ))) ≠ (2 : ℝ) := by
  norm_num [Finset.sum_const]
