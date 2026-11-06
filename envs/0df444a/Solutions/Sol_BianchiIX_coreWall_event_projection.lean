-- Prove2me | solution 1 for BianchiIX.coreWall_event_projection
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:02:38.443286+00:00
-- url     : https://prove2.me/submissions/b2303bbf-3c36-4d8b-8d60-cfb6d6cb5db5

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Theorems.Thm_BianchiIX_projectiveCoreAngle_fderiv_field
import Theorems.Thm_BianchiIX_projective_event_differential
import Theorems.Thm_BianchiIX_projective_inverse_scale
import Theorems.Thm_BianchiIX_toCoreAngleState_fderiv_field
import Theorems.Thm_BianchiIX_toProjectiveState_fderiv_field
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Module
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open BianchiIX

private theorem BianchiIX.coreClockProjection_add_field {y : ProjectiveState} (hv : 0 < y 2)
    (hd : coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3) ≠ 0)
    (v : ProjectiveState) (a : ℝ) :
    coreClockProjection y (v + a • projectiveOriginalField y) = coreClockProjection y v := by
  simp only [coreClockProjection, map_add, map_smul, toCoreAngleState_fderiv_field hv hd,
    projectiveCoreAngle_fderiv_field hv]
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem solution {x : NormalizedState} {t₀ t : ℝ}
    (hA : 1 + normalizedMaxCurve x t₀ t 0 ≠ 0)
    (hc : stateConstraint (normalizedMaxCurve x t₀ t) = 1)
    (hV : 0 < toProjectiveState (normalizedMaxCurve x t₀ t) 2)
    (hd : coreClockFactor
      (coreRadius (toProjectiveState (normalizedMaxCurve x t₀ t) 0)
        (toProjectiveState (normalizedMaxCurve x t₀ t) 2))
      (toProjectiveState (normalizedMaxCurve x t₀ t) 1)
      (toProjectiveState (normalizedMaxCurve x t₀ t) 3) ≠ 0)
    (hv : projectiveField (toProjectiveState (normalizedMaxCurve x t₀ t)) 2 ≠ 0)
    (v : NormalizedState) :
    let X := normalizedMaxCurve x t₀ t
    let y := toProjectiveState X
    let w := fderiv ℝ toProjectiveState X (normalizedEventDifferential projectiveActiveWall x t₀ t v)
    w 2 = 0 ∧ coreClockProjection y w =
      coreClockProjection y (fderiv ℝ toProjectiveState X (normalizedFlowDifferential x t₀ t v)) := by
  intro X y w
  have hproj := projective_event_differential hA hc hv v
  dsimp only at hproj
  constructor
  · change (fderiv ℝ toProjectiveState X (normalizedEventDifferential projectiveActiveWall x t₀ t v)) 2 = 0
    rw [hproj]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hv, sub_self]
  · have hpush : fderiv ℝ toProjectiveState X (normalizedField X) = projectiveOriginalField y := by
      have hs : 6 / projectiveStateDenom y = 1 + X 0 := projective_inverse_scale hA hc
      rw [toProjectiveState_fderiv_field hA hc, projectiveOriginalField, hs]
    have hw : w = fderiv ℝ toProjectiveState X (normalizedFlowDifferential x t₀ t v) +
        (normalizedEventTimeDifferential projectiveActiveWall x t₀ t v) • projectiveOriginalField y := by
      simp only [w, normalizedEventDifferential, add_apply,
        ContinuousLinearMap.smulRight_apply]
      rw [map_add, map_smul, hpush]
    rw [hw]
    exact coreClockProjection_add_field hV hd _ _
