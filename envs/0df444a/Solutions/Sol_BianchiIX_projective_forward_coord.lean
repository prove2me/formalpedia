-- Prove2me | solution 1 for BianchiIX.projective_forward_coord
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:07:35.949078+00:00
-- url     : https://prove2.me/submissions/afe3c6fa-5176-4ce8-8537-29984e0a0543

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


theorem solution {A z : ℝ} (hA : A ≠ 0) :
    projectiveCoord (A - 1) (A * z / Real.sqrt 3) = z := by
  have hr : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  unfold projectiveCoord
  rw [show 1 + (A - 1) = A by ring]
  field_simp
