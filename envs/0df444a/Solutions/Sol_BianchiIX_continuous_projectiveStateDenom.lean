-- Prove2me | solution 1 for BianchiIX.continuous_projectiveStateDenom
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:21:04.956325+00:00
-- url     : https://prove2.me/submissions/00445204-526a-481f-88bf-e1d7321b271f

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
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


theorem solution : Continuous projectiveStateDenom := by
  unfold projectiveStateDenom projectiveDenom curvature
  fun_prop
