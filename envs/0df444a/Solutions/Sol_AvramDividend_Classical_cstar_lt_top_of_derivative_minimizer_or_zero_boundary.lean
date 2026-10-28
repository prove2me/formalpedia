-- Prove2me | solution 1 for AvramDividend.Classical.cstar_lt_top_of_derivative_minimizer_or_zero_boundary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:19:50.978194+00:00
-- url     : https://prove2.me/submissions/3bfb5c80-d852-4721-9fb7-d3271543269e

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top_iff_minimizer_or_zero_boundary
import Mathlib.Data.EReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped ENNReal

theorem solution
    (W : ℝ → ℝ)
    (hcases : (∃ a : ℝ, 0 < a ∧ ∀ x : ℝ, 0 < x → deriv W a ≤ deriv W x) ∨
      ∀ x : ℝ, 0 < x → derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal)) :
    cstar W < ⊤ := by
  apply (cstar_lt_top_iff_minimizer_or_zero_boundary W).2
  rcases hcases with hmin | hzero
  · left
    change (cstarSet W).Nonempty at hmin
    exact hmin
  · exact Or.inr hzero
