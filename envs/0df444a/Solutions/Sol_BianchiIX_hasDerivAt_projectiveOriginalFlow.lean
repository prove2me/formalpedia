-- Prove2me | solution 1 for BianchiIX.hasDerivAt_projectiveOriginalFlow
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:00:09.053196+00:00
-- url     : https://prove2.me/submissions/7cf08fbd-6625-4c15-b7ab-ea08e663c353

import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Theorems.Thm_BianchiIX_hasDerivAt_toProjectiveState_normalized
import Theorems.Thm_BianchiIX_projective_inverse_scale
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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section
open BianchiIX


theorem solution {alpha : ℝ → NormalizedState} {t : ℝ}
    (hα : HasDerivAt alpha (normalizedField (alpha t)) t)
    (hA : 1 + alpha t 0 ≠ 0) (hc : stateConstraint (alpha t) = 1) :
    HasDerivAt (fun s => toProjectiveState (alpha s))
      (projectiveOriginalField (toProjectiveState (alpha t))) t := by
  have hs : 6 / projectiveStateDenom (toProjectiveState (alpha t)) = 1 + alpha t 0 :=
    projective_inverse_scale hA hc
  rw [projectiveOriginalField, hs]
  exact hasDerivAt_toProjectiveState_normalized hα hA hc
