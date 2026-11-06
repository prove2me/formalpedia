-- Prove2me | solution 1 for BianchiIX.projectiveDenom_eq
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:09:33.591323+00:00
-- url     : https://prove2.me/submissions/9ee3539e-d6a4-427d-abff-5dd78a1bc39a

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


theorem solution (m u v w : ℝ) :
    projectiveDenom m u v w = 3 + m ^ 2 + u ^ 2 + (v - w) ^ 2 - 2 * u * (v + w) := by
  unfold projectiveDenom curvature
  ring
