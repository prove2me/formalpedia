-- Prove2me | solution 1 for BianchiIX.coreRadiusReturn_exit_chart
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:02:57.025896+00:00
-- url     : https://prove2.me/submissions/2d140ab7-ca0e-480e-bfe1-381a5c22ec4c

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Theorems.Thm_BianchiIX_coreTailEntry_of_exit
import Theorems.Thm_BianchiIX_core_section_downward_phase
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_projectiveActiveWall_fderiv_field
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant

noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreRadiusReturnValid_denom_pos {Y : CoreAngleState} (H : coreRadiusReturnValid Y) :
    0 < projectiveStateDenom (coreRadiusEntry Y) := by
  have hzero := (H.2.1 0 ⟨le_rfl, H.1.1.1.le⟩).2
  rw [normalizedMaxCurve_initial] at hzero
  change 0 < 1 + (6 / projectiveStateDenom (coreRadiusEntry Y) - 1) at hzero
  by_contra! hn
  have HD := div_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 6) hn
  linarith only [hzero, HD]

/-- The canonical core output is the actual initial state of its subsequent connection. -/
theorem solution {Y : CoreAngleState} (H : coreRadiusReturnValid Y)
    (hr : 2 ≤ coreReturnState coreRadiusReturnTime Y 0)
    (hu : 0 ≤ coreReturnState coreRadiusReturnTime Y 1 ∧ coreReturnState coreRadiusReturnTime Y 1 ≤ 1 / 4)
    (hw : 0 ≤ coreReturnState coreRadiusReturnTime Y 2 ∧ coreReturnState coreRadiusReturnTime Y 2 ≤ 1 / 4) :
    coreTailEntry (coreReturnState coreRadiusReturnTime Y) =
      projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreRadiusReturnTime Y) := by
  let x := fromProjectiveState (coreRadiusEntry Y)
  let T := coreRadiusReturnTime Y
  let y := projectiveOriginalFlow (coreRadiusEntry Y) 0 T
  have hD := coreRadiusReturnValid_denom_pos H
  have hc := fromProjectiveState_constraint hD.ne'
  have hT : 0 < T := H.1.1.1
  have hA : 0 < 1 + normalizedMaxCurve x 0 T 0 := (H.2.1 T ⟨hT.le, le_rfl⟩).2
  have hcT := (normalizedMaxCurve_forward_of_constraint hc hT.le).2.1
  have hv : y 2 = 1 := H.1.1.2.2
  have hn := H.2.2.2
  rw [normalizedEventRate, projectiveActiveWall_fderiv_field hA.ne' hcT] at hn
  have hvel : activeVelocity (y 0) (y 1) 1 (y 3) < 0 := by
    have HH : projectiveField y 2 < 0 := by
      by_contra! hh
      exact (not_le_of_gt hn) (mul_nonneg hA.le hh)
    change activeVelocity (y 0) (y 1) (y 2) (y 3) < 0 at HH
    rwa [hv] at HH
  have hw' : 0 ≤ y 3 ∧ y 3 ≤ 1 / 4 := by
    change 0 ≤ y 2 * y 3 ∧ y 2 * y 3 ≤ 1 / 4 at hw
    simpa only [hv, one_mul] using hw
  have hr' : 2 ≤ coreRadius (y 0) 1 := by
    change 2 ≤ coreRadius (y 0) (y 2) at hr
    rwa [hv] at hr
  exact coreTailEntry_of_exit (core_section_downward_phase hr' hu hw' hvel) hv
