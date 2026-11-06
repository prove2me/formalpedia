-- Prove2me | solution 1 for BianchiIX.constraint_of_projective
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:12:27.171213+00:00
-- url     : https://prove2.me/submissions/354ec1ef-7dce-4ada-b907-0bfc1c9f5893

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
    {A m u v w : ℝ} (hD : A * projectiveDenom m u v w = 6) :
    constraint (A - 1) (A * m / Real.sqrt 3) (A * u / Real.sqrt 3)
      (A * v / Real.sqrt 3) (A * w / Real.sqrt 3) = 1 := by
  have hr : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hr2 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold constraint shearSq curvature
  field_simp
  ring_nf
  rw [hr2]
  unfold projectiveDenom curvature at hD
  nlinarith only [congrArg (fun x => A * x) hD]
