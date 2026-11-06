-- Prove2me | solution 1 for BianchiIX.isOpen_positiveWalls
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T13:56:48.116193+00:00
-- url     : https://prove2.me/submissions/f56be123-122b-4cf9-8cf0-5a07cb623de0

import Definitions.Def_BianchiIX_Dynamics_Normalized
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

noncomputable section
open BianchiIX
open Set


theorem solution : IsOpen {x : NormalizedState | positiveWalls x} :=
  (isOpen_lt continuous_const (continuous_apply 2)).inter
    ((isOpen_lt continuous_const (continuous_apply 3)).inter
      (isOpen_lt continuous_const (continuous_apply 4)))
