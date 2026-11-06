-- Prove2me | solution 1 for BianchiIX.projective_inverse_coord
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:07:10.324407+00:00
-- url     : https://prove2.me/submissions/c69091a9-01d0-4697-a4f9-dd2fc192ad0b

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


theorem solution {p z : ℝ} (hA : 1 + p ≠ 0) :
    (1 + p) * projectiveCoord p z / Real.sqrt 3 = z := by
  have hr : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  unfold projectiveCoord
  field_simp
