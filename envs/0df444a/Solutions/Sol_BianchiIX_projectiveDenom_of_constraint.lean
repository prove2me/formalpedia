-- Prove2me | solution 1 for BianchiIX.projectiveDenom_of_constraint
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:06:55.340752+00:00
-- url     : https://prove2.me/submissions/6822c8b0-eb6f-4915-bc44-b436a071191b

import Definitions.Def_BianchiIX_Algebra_Coordinates
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
    {p s a b c : ℝ} (hA : 1 + p ≠ 0) (hG : constraint p s a b c = 1) :
    projectiveDenom (projectiveCoord p s) (projectiveCoord p a)
      (projectiveCoord p b) (projectiveCoord p c) = 6 / (1 + p) := by
  have hr : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold projectiveDenom projectiveCoord curvature
  field_simp
  ring_nf
  rw [hr]
  unfold constraint shearSq curvature at hG
  nlinarith only [hG]
