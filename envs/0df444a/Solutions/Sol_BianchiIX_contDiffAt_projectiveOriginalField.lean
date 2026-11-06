-- Prove2me | solution 1 for BianchiIX.contDiffAt_projectiveOriginalField
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:54:36.086599+00:00
-- url     : https://prove2.me/submissions/1dddea20-c8c3-427e-aa6d-cd6f7b8ddeef

import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Theorems.Thm_BianchiIX_contDiff_projectiveField
import Theorems.Thm_BianchiIX_contDiff_projectiveStateDenom
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


theorem solution (n : WithTop ℕ∞) {y : ProjectiveState}
    (hD : projectiveStateDenom y ≠ 0) : ContDiffAt ℝ n projectiveOriginalField y := by
  have hd := (contDiff_projectiveStateDenom n).contDiffAt (x := y)
  have hf := (contDiff_projectiveField n).contDiffAt (x := y)
  unfold projectiveOriginalField
  fun_prop
