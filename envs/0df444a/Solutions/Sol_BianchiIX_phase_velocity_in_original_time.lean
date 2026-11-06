-- Prove2me | solution 1 for BianchiIX.phase_velocity_in_original_time
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:14:01.085879+00:00
-- url     : https://prove2.me/submissions/d2fc77b5-4b8d-4aaf-a372-c5b6029dc9a6

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
    {p s a b c : ℝ} (hA : 1 + p ≠ 0) :
    Real.sqrt 3 * (shearMinus s a b c * (1 + p) - s * shearPlus p a b c) /
      (1 + p) ^ 2 = (1 + p) * phaseVelocity
        (projectiveCoord p s) (projectiveCoord p a) (projectiveCoord p b)
        (projectiveCoord p c) := by
  have hr : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold projectiveCoord phaseVelocity coupling shearMinus shearPlus curvature
  field_simp
  ring_nf
  rw [hr]
