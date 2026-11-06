-- Prove2me | solution 1 for BianchiIX.contDiff_projectiveStateDenom
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:25:40.260529+00:00
-- url     : https://prove2.me/submissions/2fd634f5-14e6-450a-9177-ca035c8dc270

import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
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


theorem solution (n : WithTop ℕ∞) :
    ContDiff ℝ n projectiveStateDenom := by
  unfold projectiveStateDenom projectiveDenom curvature
  fun_prop
