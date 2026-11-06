-- Prove2me | solution 1 for BianchiIX.coreRadiusReturn_reference_regular
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:31:25.568123+00:00
-- url     : https://prove2.me/submissions/fe1be462-b478-4d76-8280-f6f83e5ca9ff

import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ReferenceSectionMap
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Theorems.Thm_BianchiIX_exists_referenceCore_firstReturn_two
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum
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
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_projectiveCoreRadius (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) : ContDiffAt ℝ n (fun z : ProjectiveState => coreRadius (z 0) (z 2)) y := by
  have he : coreEnergy (y 0) (y 2) ≠ 0 := by unfold coreEnergy; positivity
  have he' : (y 0 - 1) ^ 2 + y 2 ^ 2 ≠ 0 := he
  unfold coreRadius coreEnergy
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_toCoreAngleState (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) : ContDiffAt ℝ n toCoreAngleState y := by
  have hr := contDiffAt_projectiveCoreRadius n hv
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [toCoreAngleState] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiff_coreSectionEmbedding (n : WithTop ℕ∞) : ContDiff ℝ n coreSectionEmbedding := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreSectionEmbedding] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiff_coreSectionCoordinates (n : WithTop ℕ∞) : ContDiff ℝ n coreSectionCoordinates := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreSectionCoordinates] <;> fun_prop

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

/-- The canonical first return agrees locally with the smooth branch near every boundary pulse. -/
theorem solution {k : ℝ} (hk : 1 < k) :
    coreRadiusReturnTime ![k, 0, 0] = referenceNormalizedTime k ∧
      ContDiffAt ℝ 2 coreRadiusReturnTime ![k, 0, 0] ∧
      ContDiffAt ℝ 2 (coreReturnState coreRadiusReturnTime) ![k, 0, 0] ∧
      (∀ᶠ Y in 𝓝 (![k, 0, 0] : CoreAngleState), coreRadiusReturnValid Y) := by
  let Y₀ : CoreAngleState := ![k, 0, 0]
  let e : CoreAngleState → CoreCoordinates := fun Y => coreSectionCoordinates (coreRadiusEntry Y)
  have hemb (Y : CoreAngleState) : coreSectionEmbedding (e Y) = coreRadiusEntry Y := by
    ext i
    fin_cases i <;> rfl
  have hchart (Y : CoreAngleState) : coreSectionChart (e Y) = fromProjectiveState (coreRadiusEntry Y) := by
    rw [coreSectionChart, hemb]
  have he₀ : e Y₀ = referenceCoreInput k := rfl
  have hce : ContDiffAt ℝ 2 e Y₀ :=
    (contDiff_coreSectionCoordinates 2).contDiffAt.comp Y₀ (contDiffAt_coreRadiusEntry 2 hk)
  obtain ⟨τ, P, hτ, hP, hcτ, hcP, hnear, _⟩ := exists_referenceCore_firstReturn_two hk
  have hnear' := hce.continuousAt.eventually (he₀.symm ▸ hnear)
  have heq : coreRadiusReturnTime =ᶠ[𝓝 Y₀] (fun Y => τ (e Y)) := by
    filter_upwards [hnear'] with Y hY
    have H := hY.1.csInf_eq
    simpa only [coreRadiusReturnTime, hchart] using H
  have hcTime : ContDiffAt ℝ 2 coreRadiusReturnTime Y₀ :=
    ((he₀.symm ▸ hcτ).comp Y₀ hce).congr_of_eventuallyEq heq
  have hfirst : ∀ᶠ Y in 𝓝 Y₀, coreRadiusReturnValid Y := by
    filter_upwards [hnear', heq] with Y hY hT
    dsimp only [coreRadiusReturnValid]
    rw [hT, ← hchart]
    exact ⟨hY.1, hY.2.1, hY.2.2.1, hY.2.2.2.1⟩
  have hcP' : ContDiffAt ℝ 2 (fun Y => P (e Y)) Y₀ := (he₀.symm ▸ hcP).comp Y₀ hce
  have hcEmb : ContDiffAt ℝ 2 (fun Y => coreSectionEmbedding (P (e Y))) Y₀ :=
    (contDiff_coreSectionEmbedding 2).contDiffAt.comp Y₀ hcP'
  have hcOut : ContDiffAt ℝ 2 (fun Y => toCoreAngleState (coreSectionEmbedding (P (e Y)))) Y₀ := by
    have hv : (0 : ℝ) < coreSectionEmbedding (P (e Y₀)) 2 := by change (0 : ℝ) < 1; norm_num
    convert! (contDiffAt_toCoreAngleState 2 hv).comp Y₀ hcEmb using 1
  have heqOut : coreReturnState coreRadiusReturnTime =ᶠ[𝓝 Y₀]
      (fun Y => toCoreAngleState (coreSectionEmbedding (P (e Y)))) := by
    filter_upwards [hnear', heq] with Y hY hT
    dsimp only [coreReturnState, projectiveOriginalFlow]
    rw [hT, ← hchart, hY.2.2.2.2]
  refine ⟨?_, hcTime, hcOut.congr_of_eventuallyEq heqOut, hfirst⟩
  exact heq.self_of_nhds.trans ((congrArg τ he₀).trans hτ)
