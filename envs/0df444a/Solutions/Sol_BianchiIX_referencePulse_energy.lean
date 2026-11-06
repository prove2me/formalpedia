-- Prove2me | solution 1 for BianchiIX.referencePulse_energy
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:46:32.789404+00:00
-- url     : https://prove2.me/submissions/bec7820c-822d-4006-aa98-47cc5028e7fe

import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
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
import Mathlib.Analysis.SpecialFunctions.Arcosh

noncomputable section
open BianchiIX


theorem solution (k t : ℝ) :
    coreEnergy (referencePulse k t 0) (referencePulse k t 2) = k ^ 2 := by
  dsimp [referencePulse, coreEnergy]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  linear_combination -k ^ 2 * Real.cosh_sq_sub_sinh_sq (k * t)
