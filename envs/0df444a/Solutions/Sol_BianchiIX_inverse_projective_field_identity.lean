-- Prove2me | solution 1 for BianchiIX.inverse_projective_field_identity
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:24:38.675903+00:00
-- url     : https://prove2.me/submissions/121841f8-133c-4cc9-9085-855b6d65604f

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

noncomputable section
open BianchiIX


theorem solution (A m u v w : ℝ)
    (hD : A * projectiveDenom m u v w = 6) :
    let B := A * coupling u v w + A ^ 2 * curvature u v w / 3
    A • ![B, (B * m + A * phaseVelocity m u v w) / Real.sqrt 3,
      (B * u + A * strongVelocity m u v w) / Real.sqrt 3,
      (B * v + A * activeVelocity m u v w) / Real.sqrt 3,
      (B * w + A * weakVelocity m u v w) / Real.sqrt 3] =
      normalizedField ![A - 1, A * m / Real.sqrt 3, A * u / Real.sqrt 3,
        A * v / Real.sqrt 3, A * w / Real.sqrt 3] := by
  have hr : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hr2 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hd : A * (3 + m ^ 2 + curvature u v w) = 6 := hD
  dsimp [curvature] at hd
  ext i
  fin_cases i <;>
    dsimp [normalizedField, shearPlus, shearMinus, rateOne, rateTwo, rateThree,
      shearSq, phaseVelocity, strongVelocity, activeVelocity, weakVelocity, coupling,
      curvature] <;>
    field_simp <;> ring_nf <;> rw [hr2] <;> ring_nf
  · linear_combination (6 * A - 9) * A * u * hd
  · linear_combination 3 * A ^ 2 * v * hd
  · linear_combination 3 * A ^ 2 * w * hd
