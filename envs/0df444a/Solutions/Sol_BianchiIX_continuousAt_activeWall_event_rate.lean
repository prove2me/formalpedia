-- Prove2me | solution 1 for BianchiIX.continuousAt_activeWall_event_rate
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T04:32:15.649937+00:00
-- url     : https://prove2.me/submissions/9cc959c2-9d7e-4183-b7f6-224e3121f47e

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_Events
import Theorems.Thm_BianchiIX_contDiffAt_projectiveActiveWall
import Theorems.Thm_BianchiIX_contDiff_normalizedField
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
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
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology


theorem solution {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) (hA : 1 + normalizedMaxCurve x t₀ t 0 ≠ 0) :
    ContinuousAt (fun z : NormalizedState × ℝ => normalizedEventRate projectiveActiveWall z.1 t₀ z.2) (x, t) := by
  have hflow := (normalizedMaxCurve_regular ht).2.continuousAt
  have hderiv := (contDiffAt_projectiveActiveWall 2 hA).continuousAt_fderiv (by norm_num)
  have hderiv' : ContinuousAt (fun z : NormalizedState × ℝ =>
      fderiv ℝ projectiveActiveWall (normalizedMaxCurve z.1 t₀ z.2)) (x, t) :=
    ContinuousAt.comp (f := fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) hderiv hflow
  have hfield : ContinuousAt (fun z : NormalizedState × ℝ =>
      normalizedField (normalizedMaxCurve z.1 t₀ z.2)) (x, t) :=
    ContinuousAt.comp (f := fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2)
      (contDiff_normalizedField 1).continuous.continuousAt hflow
  exact hderiv'.clm_apply hfield
