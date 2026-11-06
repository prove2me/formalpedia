-- Prove2me | solution 1 for BianchiIX.coreEntryLogRate_parameter_derivative
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:00:39.577207+00:00
-- url     : https://prove2.me/submissions/7fe9b04c-e846-433a-82d0-21e61b5beb8a

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreMultipliers
import Theorems.Thm_BianchiIX_contDiffAt_coreOriginalLogRates
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
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
open Set Filter MeasureTheory
open scoped Topology

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasFDerivAt_normalizedMaxCurve_initial {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    HasFDerivAt (fun y => normalizedMaxCurve y t₀ t) (normalizedFlowDifferential x t₀ t) x := by
  have H := (normalizedMaxCurve_regular ht).2.comp x (contDiffAt_id.prodMk contDiffAt_const)
  exact (H.differentiableAt (by norm_num)).hasFDerivAt

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasFDerivAt_projectiveOriginalFlow_initial {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) :
    HasFDerivAt (fun z => projectiveOriginalFlow z t₀ t) (projectiveFlowDifferential y t₀ t) y := by
  have hfrom := ((contDiffAt_fromProjectiveState 1 (ne_of_gt hD)).differentiableAt (by norm_num)).hasFDerivAt
  have hto := ((contDiffAt_toProjectiveState 1 (ne_of_gt hA)).differentiableAt (by norm_num)).hasFDerivAt
  exact hto.comp y ((hasFDerivAt_normalizedMaxCurve_initial ht).comp y hfrom)

end
end

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

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.contDiffAt_coreRadius_flow {Y : CoreAngleState} {t : ℝ}
    (hk : 1 < Y 0) (hD : 0 < projectiveStateDenom (coreRadiusEntry Y))
    (ht : t ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 t 0) :
    ContDiffAt ℝ 1 (fun p : CoreAngleState × ℝ => projectiveOriginalFlow (coreRadiusEntry p.1) 0 p.2)
      (Y, t) := by
  have he := (contDiffAt_fromProjectiveState 1 (ne_of_gt hD)).comp Y (contDiffAt_coreRadiusEntry 1 hk)
  have hp : ContDiffAt ℝ 1 (fun p : CoreAngleState × ℝ =>
      (fromProjectiveState (coreRadiusEntry p.1), p.2)) (Y, t) :=
    (he.comp (Y, t) contDiffAt_fst).prodMk contDiffAt_snd
  have hf := (normalizedMaxCurve_regular ht).2.comp (Y, t)
    (g := fun p : NormalizedState × ℝ => normalizedMaxCurve p.1 0 p.2)
    (f := fun p : CoreAngleState × ℝ => (fromProjectiveState (coreRadiusEntry p.1), p.2)) hp
  exact (contDiffAt_toProjectiveState 1 (ne_of_gt hA)).comp (Y, t) hf

end
end

private theorem BianchiIX.contDiffAt_coreEntryLogRates {Y : CoreAngleState} {t : ℝ}
    (hk : 1 < Y 0) (hD : 0 < projectiveStateDenom (coreRadiusEntry Y))
    (ht : t ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 t 0)
    (hV : 0 < projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2)
    (hDz : projectiveStateDenom (projectiveOriginalFlow (coreRadiusEntry Y) 0 t) ≠ 0)
    (hd : let z := projectiveOriginalFlow (coreRadiusEntry Y) 0 t
      coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3) ≠ 0) :
    ContDiffAt ℝ 1 (fun p : CoreAngleState × ℝ =>
      coreOriginalLogRates (projectiveOriginalFlow (coreRadiusEntry p.1) 0 p.2)) (Y, t) :=
  (contDiffAt_coreOriginalLogRates 1 hV hDz hd).comp (Y, t) (g := coreOriginalLogRates)
    (f := fun p : CoreAngleState × ℝ => projectiveOriginalFlow (coreRadiusEntry p.1) 0 p.2)
    (contDiffAt_coreRadius_flow hk hD ht hA)

theorem solution {Y : CoreAngleState} {t : ℝ}
    (hk : 1 < Y 0) (hD : 0 < projectiveStateDenom (coreRadiusEntry Y))
    (ht : t ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 t 0)
    (hV : 0 < projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2)
    (hDz : projectiveStateDenom (projectiveOriginalFlow (coreRadiusEntry Y) 0 t) ≠ 0)
    (hd : let z := projectiveOriginalFlow (coreRadiusEntry Y) 0 t
      coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3) ≠ 0) (v : CoreAngleState) (i : Fin 2) :
    fderiv ℝ (fun p : CoreAngleState × ℝ =>
      coreOriginalLogRates (projectiveOriginalFlow (coreRadiusEntry p.1) 0 p.2) i) (Y, t) (v, 0) =
      (fderiv ℝ coreOriginalLogRates (projectiveOriginalFlow (coreRadiusEntry Y) 0 t)
        (projectiveFlowDifferential (coreRadiusEntry Y) 0 t (fderiv ℝ coreRadiusEntry Y v))) i := by
  have hFc := contDiffAt_pi.mp (contDiffAt_coreEntryLogRates hk hD ht hA hV hDz hd) i
  have hF := hFc.differentiableAt (by norm_num)
  have hleft := hF.hasFDerivAt.comp Y (hasFDerivAt_prodMk_left (𝕜 := ℝ) Y t)
  have hrate := hasFDerivAt_pi'.mp
    ((contDiffAt_coreOriginalLogRates 1 hV hDz hd).differentiableAt (by norm_num)).hasFDerivAt i
  have hentry := ((contDiffAt_coreRadiusEntry 1 hk).differentiableAt (by norm_num)).hasFDerivAt
  have hright := hrate.comp Y ((hasFDerivAt_projectiveOriginalFlow_initial hD ht hA).comp Y hentry)
  exact congrArg (fun A : CoreAngleState →L[ℝ] ℝ => A v) (hleft.unique hright)
