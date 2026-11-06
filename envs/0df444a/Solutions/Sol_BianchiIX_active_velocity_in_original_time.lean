-- Prove2me | solution 1 for BianchiIX.active_velocity_in_original_time
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:15:25.185423+00:00
-- url     : https://prove2.me/submissions/a0d5996f-1767-4e25-b6d1-05f628e55051

import Definitions.Def_BianchiIX_Algebra_Projective
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
    Real.sqrt 3 * ((rateTwo p s * b) * (1 + p) - b * shearPlus p a b c) /
      (1 + p) ^ 2 = (1 + p) * activeVelocity
        (projectiveCoord p s) (projectiveCoord p a) (projectiveCoord p b)
        (projectiveCoord p c) := by
  have hr : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold projectiveCoord activeVelocity coupling rateTwo shearSq shearPlus curvature
  field_simp
  ring_nf
  rw [hr]
  unfold constraint shearSq curvature at hG
  linear_combination -b * (1 + p) * hG
