-- Prove2me | solution 1 for BianchiIX.projectiveDenom_positive
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:26:44.851726+00:00
-- url     : https://prove2.me/submissions/ea7b75fa-8216-424b-bff6-eed93b609cfd

import Definitions.Def_BianchiIX_Algebra_Coordinates
import Theorems.Thm_BianchiIX_projectiveDenom_of_constraint
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

open BianchiIX
noncomputable section


theorem solution
    {p s a b c : ℝ} (hA : 0 < 1 + p) (hG : constraint p s a b c = 1) :
    0 < projectiveDenom (projectiveCoord p s) (projectiveCoord p a)
      (projectiveCoord p b) (projectiveCoord p c) := by
  rw [projectiveDenom_of_constraint (ne_of_gt hA) hG]
  exact div_pos (by norm_num) hA
