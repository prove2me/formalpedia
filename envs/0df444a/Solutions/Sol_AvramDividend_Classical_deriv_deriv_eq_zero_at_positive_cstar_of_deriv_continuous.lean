-- Prove2me | solution 1 for AvramDividend.Classical.deriv_deriv_eq_zero_at_positive_cstar_of_deriv_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T07:20:38.301121+00:00
-- url     : https://prove2.me/submissions/a21b6ef4-91c8-432c-b0bc-b1dbee40412c

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_toReal_zero_or_minimal_of_deriv_continuous
import Theorems.Thm_AvramDividend_Classical_deriv_deriv_eq_zero_of_mem_cstarSet

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution (W : ℝ → ℝ)
    (hcont : ContinuousOn (deriv W) (Ioi 0))
    (hpos : 0 < (cstar W).toReal) :
    deriv (deriv W) (cstar W).toReal = 0 := by
  rcases cstar_toReal_zero_or_minimal_of_deriv_continuous W hcont with
    hz | ⟨hp, hmin⟩
  · exact False.elim ((ne_of_gt hpos) hz)
  · apply deriv_deriv_eq_zero_of_mem_cstarSet W (cstar W).toReal
    change 0 < (cstar W).toReal ∧
      ∀ x : ℝ, 0 < x → deriv W (cstar W).toReal ≤ deriv W x
    exact ⟨hp, hmin⟩
