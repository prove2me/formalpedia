-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_deriv_one_of_regular_minimal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T08:45:33.720354+00:00
-- url     : https://prove2.me/submissions/e6e4fe5b-10b7-42d7-be2a-175159e2db83

import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one_of_regular_minimal
import Theorems.Thm_AvramDividend_Classical_barrierValue_deriv_one_of_differentiableAt
import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set
open scoped NNReal ENNReal

theorem solution
    (W : ℝ → ℝ)
    (ha : 0 < (cstar W).toReal)
    (hreg : ContDiffOn ℝ 1 W (Set.Ioi 0))
    (hpos : ∀ x : ℝ, 0 < x → 0 < deriv W x)
    (hmin : (cstar W).toReal = 0 ∨
      (0 < (cstar W).toReal ∧
       ∀ x : ℝ, 0 < x → deriv W (cstar W).toReal ≤ deriv W x)) :
    deriv (vcstar W) (cstar W).toReal = 1 := by
  have hdiff : DifferentiableAt ℝ (vcstar W) (cstar W).toReal :=
    (vcstar_deriv_ge_one_of_regular_minimal W hreg hpos hmin _ ha).1
  change deriv (barrierValue W (cstar W).toReal) (cstar W).toReal = 1
  exact barrierValue_deriv_one_of_differentiableAt
    W (cstar W).toReal (le_of_lt ha) hdiff
