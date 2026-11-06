-- Prove2me | solution 1 for BianchiIX.projective_event_differential
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:44:56.573405+00:00
-- url     : https://prove2.me/submissions/423b98ff-c28c-4a3d-be4d-5c9a372e980b

import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ReferenceEvents
import Theorems.Thm_BianchiIX_projectiveActiveWall_fderiv
import Theorems.Thm_BianchiIX_projectiveActiveWall_fderiv_field
import Theorems.Thm_BianchiIX_toProjectiveState_fderiv_field
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

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology


theorem solution {x : NormalizedState} {t₀ t : ℝ}
    (hA : 1 + normalizedMaxCurve x t₀ t 0 ≠ 0)
    (hc : stateConstraint (normalizedMaxCurve x t₀ t) = 1)
    (hv : projectiveField (toProjectiveState (normalizedMaxCurve x t₀ t)) 2 ≠ 0)
    (v : NormalizedState) :
    let y := normalizedMaxCurve x t₀ t
    let xi := fderiv ℝ toProjectiveState y (normalizedFlowDifferential x t₀ t v)
    fderiv ℝ toProjectiveState y (normalizedEventDifferential projectiveActiveWall x t₀ t v) =
      xi - (xi 2 / projectiveField (toProjectiveState y) 2) • projectiveField (toProjectiveState y) := by
  dsimp only
  change fderiv ℝ toProjectiveState (normalizedMaxCurve x t₀ t)
    (normalizedFlowDifferential x t₀ t v +
      (-(fderiv ℝ projectiveActiveWall (normalizedMaxCurve x t₀ t)
        (normalizedField (normalizedMaxCurve x t₀ t)))⁻¹ *
          fderiv ℝ projectiveActiveWall (normalizedMaxCurve x t₀ t)
            (normalizedFlowDifferential x t₀ t v)) • normalizedField (normalizedMaxCurve x t₀ t)) = _
  rw [map_add, map_smul]
  rw [projectiveActiveWall_fderiv_field hA hc,
    projectiveActiveWall_fderiv hA, toProjectiveState_fderiv_field hA hc]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring
