-- Prove2me | solution 1 for BianchiIX.referencePulse_active_pos
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:46:39.130019+00:00
-- url     : https://prove2.me/submissions/f333d05c-4f08-4676-8628-a4c12c4ca795

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


theorem solution {k : ℝ} (hk : 0 < k) (t : ℝ) :
    0 < referencePulse k t 2 := div_pos hk (Real.cosh_pos _)
