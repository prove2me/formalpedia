-- Prove2me | solution 1 for BianchiIX.coreReturn_exit_angle_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:04:02.745307+00:00
-- url     : https://prove2.me/submissions/7941297e-f4d1-4c68-9e53-e313ce2a1029

import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_CoreExitFactor
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Theorems.Thm_BianchiIX_coreRegion_exit_angle_bound
import Theorems.Thm_BianchiIX_exists_coreExit_event
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
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
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_coreRadiusEntry (n : WithTop ℕ∞) {Y : CoreAngleState} (hk : 1 < Y 0) :
    ContDiffAt ℝ n coreRadiusEntry Y := by
  have hs : Y 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith only [hk] : 0 < Y 0 ^ 2 - 1)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreRadiusEntry] <;> fun_prop

end
end

/-- Local event uniqueness identifies derivatives of any continuous hitting-time branch. -/
theorem solution {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hk : 6 ≤ Y 0) (hD : 0 < projectiveStateDenom (coreRadiusEntry Y))
    (hτ : ContinuousAt τ Y)
    (ht : τ Y ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 (τ Y) 0)
    (hcore : coreRegion (Y 0) (projectiveOriginalFlow (coreRadiusEntry Y) 0 (τ Y)))
    (hhit : ∀ᶠ Z in 𝓝 Y, projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 2 = 1)
    (hM : projectiveOriginalFlow (coreRadiusEntry Y) 0 (τ Y) 0 < 1)
    (v : CoreAngleState) :
    |fderiv ℝ (fun Z => projectiveCoreAngle (projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z))) Y v| ≤
      2 * |coreProjectedFlowVariation (coreRadiusEntry Y) 0 (τ Y)
        (fderiv ℝ coreRadiusEntry Y v) 0| / Y 0 := by
  have hV := hhit.self_of_nhds
  obtain ⟨σ, _, _, _, huniq, _, hcZ, hderiv⟩ :=
    exists_coreExit_event hk hD ht hA hcore hV hM
  have hentry := contDiffAt_coreRadiusEntry 1 (by linarith only [hk] : 1 < Y 0)
  have hpair : ContinuousAt (fun Z => (coreRadiusEntry Z, τ Z)) Y :=
    hentry.continuousAt.prodMk hτ
  have heq : (fun Z => projectiveCoreAngle (projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z))) =ᶠ[𝓝 Y]
      (fun Z => projectiveCoreAngle (projectiveOriginalFlow (coreRadiusEntry Z) 0 (σ (coreRadiusEntry Z)))) := by
    filter_upwards [hpair.eventually huniq, hhit] with Z hZ hh
    rw [(hZ.2.mp hh).symm]
  have hchain := ((hcZ.differentiableAt (by norm_num)).hasFDerivAt).comp Y
    ((hentry.differentiableAt (by norm_num)).hasFDerivAt)
  change HasFDerivAt
    (fun Z => projectiveCoreAngle (projectiveOriginalFlow (coreRadiusEntry Z) 0 (σ (coreRadiusEntry Z)))) _ Y at hchain
  rw [heq.fderiv_eq, hchain.fderiv, ContinuousLinearMap.comp_apply, (hderiv (fderiv ℝ coreRadiusEntry Y v)).1]
  exact coreRegion_exit_angle_bound hk hcore hV hM _
