-- Prove2me | solution 1 for BianchiIX.contDiff_projectiveField
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:47:36.92408+00:00
-- url     : https://prove2.me/submissions/a098b134-24f9-46b2-917c-b8b72c7188e8

import Definitions.Def_BianchiIX_Dynamics_ProjectiveLinearization
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


theorem solution (n : WithTop ℕ∞) : ContDiff ℝ n projectiveField := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;>
    dsimp [projectiveField, phaseVelocity, strongVelocity, activeVelocity, weakVelocity, coupling] <;>
    fun_prop
