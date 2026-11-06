-- Prove2me | solution 1 for BianchiIX.projective_inverse_scale
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:26:29.098031+00:00
-- url     : https://prove2.me/submissions/2435e649-a4a7-4c1a-9334-128017aabd99

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
    {p s a b c : ℝ} (hA : 1 + p ≠ 0) (hG : constraint p s a b c = 1) :
    6 / projectiveDenom (projectiveCoord p s) (projectiveCoord p a)
      (projectiveCoord p b) (projectiveCoord p c) = 1 + p := by
  rw [projectiveDenom_of_constraint hA hG]
  field_simp
