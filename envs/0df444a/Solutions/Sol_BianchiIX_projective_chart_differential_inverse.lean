-- Prove2me | solution 1 for BianchiIX.projective_chart_differential_inverse
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:44:03.953046+00:00
-- url     : https://prove2.me/submissions/79438524-925d-4427-9a0e-40413eb0c35f

import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_continuous_projectiveStateDenom
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
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
import Mathlib.Analysis.Calculus.FDeriv.Partial

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology


theorem solution {y : ProjectiveState}
    (hD : 0 < projectiveStateDenom y) :
    (fderiv ℝ toProjectiveState (fromProjectiveState y)).comp (fderiv ℝ fromProjectiveState y) =
      ContinuousLinearMap.id ℝ ProjectiveState := by
  have hfrom := ((contDiffAt_fromProjectiveState 1 (ne_of_gt hD)).differentiableAt (by norm_num)).hasFDerivAt
  have hto := ((contDiffAt_toProjectiveState 1 (ne_of_gt (fromProjectiveState_clock_pos hD))).differentiableAt
    (by norm_num)).hasFDerivAt
  have heq : (fun z => toProjectiveState (fromProjectiveState z)) =ᶠ[𝓝 y] id := by
    filter_upwards [continuous_projectiveStateDenom.continuousAt.eventually_ne (ne_of_gt hD)] with z hz
    exact toProjectiveState_fromProjectiveState hz
  exact ((hto.comp y hfrom).congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_id y)
