-- Prove2me | solution 1 for BianchiIX.coreRadiusReturn_reference_wall_derivative
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:38:37.488464+00:00
-- url     : https://prove2.me/submissions/6d7b0cde-eb57-48c5-a97c-2257bf63e879

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ReferenceSectionMap
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Theorems.Thm_BianchiIX_coreRadiusEntry_fderiv
import Theorems.Thm_BianchiIX_coreRadiusReturn_reference_regular
import Theorems.Thm_BianchiIX_coreSectionCoordinates_fderiv
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
open Set Filter
open scoped Topology

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

/-- The transverse rows in radius coordinates retain the two exact reference multipliers. -/
theorem solution {k : ℝ} (hk : 1 < k) (v : CoreAngleState) :
    (fderiv ℝ (coreReturnState coreRadiusReturnTime) ![k, 0, 0] v) 1 =
        Real.exp (-k * Real.arcosh k) * v 1 ∧
      (fderiv ℝ (coreReturnState coreRadiusReturnTime) ![k, 0, 0] v) 2 =
        Real.exp (-4 * Real.arcosh k / k) * v 2 := by
  let Y₀ : CoreAngleState := ![k, 0, 0]
  let e : CoreAngleState → CoreCoordinates := fun Y => coreSectionCoordinates (coreRadiusEntry Y)
  have hemb (Y : CoreAngleState) : coreSectionEmbedding (e Y) = coreRadiusEntry Y := by
    ext i
    fin_cases i <;> rfl
  have hchart (Y : CoreAngleState) : coreSectionChart (e Y) = fromProjectiveState (coreRadiusEntry Y) := by
    rw [coreSectionChart, hemb]
  have he₀ : e Y₀ = referenceCoreInput k := rfl
  have hce : ContDiffAt ℝ 1 e Y₀ :=
    (contDiff_coreSectionCoordinates 1).contDiffAt.comp Y₀ (contDiffAt_coreRadiusEntry 1 hk)
  have hde : fderiv ℝ e Y₀ v = ![k / Real.sqrt (k ^ 2 - 1) * v 0, v 1, v 2] := by
    have H := fderiv_comp Y₀ ((contDiff_coreSectionCoordinates 1).differentiable (by norm_num) _)
      ((contDiffAt_coreRadiusEntry 1 hk).differentiableAt (by norm_num))
    change fderiv ℝ e Y₀ = _ at H
    rw [H, ContinuousLinearMap.comp_apply, coreSectionCoordinates_fderiv, coreRadiusEntry_fderiv hk]
    rfl
  obtain ⟨τ, P, _, _, _, hcP, hnear, hdP⟩ := exists_referenceCore_firstReturn_two hk
  have hnear' := hce.continuousAt.eventually (he₀.symm ▸ hnear)
  have heq (i : Fin 2) : (fun Y => coreReturnState coreRadiusReturnTime Y i.succ) =ᶠ[𝓝 Y₀]
      (fun Y => P (e Y) i.succ) := by
    filter_upwards [hnear'] with Y hY
    have hT : coreRadiusReturnTime Y = τ (e Y) := by
      simpa only [coreRadiusReturnTime, hchart] using hY.1.csInf_eq
    dsimp only [coreReturnState, projectiveOriginalFlow]
    rw [hT, ← hchart, hY.2.2.2.2]
    fin_cases i
    · rfl
    · exact one_mul (P (e Y) 2)
  have hcF := (coreRadiusReturn_reference_regular hk).2.2.1
  have hdF := (hcF.differentiableAt (by norm_num)).hasFDerivAt
  have hdPe := ((he₀.symm ▸ hcP).differentiableAt (by norm_num)).hasFDerivAt.comp Y₀
    (hce.differentiableAt (by norm_num)).hasFDerivAt
  have H (i : Fin 2) :
      (fderiv ℝ (coreReturnState coreRadiusReturnTime) Y₀ v) i.succ =
        (fderiv ℝ P (referenceCoreInput k) (fderiv ℝ e Y₀ v)) i.succ := by
    have hleft := (hasFDerivAt_apply (𝕜 := ℝ) i.succ (coreReturnState coreRadiusReturnTime Y₀)).comp Y₀ hdF
    have hright := (hasFDerivAt_apply (𝕜 := ℝ) i.succ (P (e Y₀))).comp Y₀ hdPe
    exact congrArg (fun L => L v) ((hleft.congr_of_eventuallyEq (heq i).symm).unique hright)
  have H₀ := H 0
  have H₁ := H 1
  rw [hdP, hde] at H₀ H₁
  exact ⟨H₀, H₁⟩
