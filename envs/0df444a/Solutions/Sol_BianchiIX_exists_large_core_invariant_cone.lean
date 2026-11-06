-- Prove2me | solution 1 for BianchiIX.exists_large_core_invariant_cone
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:34:19.249695+00:00
-- url     : https://prove2.me/submissions/55179f0c-0456-469b-ada3-a091ca0d9f69

import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreMultipliers
import Definitions.Def_BianchiIX_Dynamics_CoreMultiplierDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Theorems.Thm_BianchiIX_coreReturnMultiplier_contraction
import Theorems.Thm_BianchiIX_coreReturnState_radius_bound
import Theorems.Thm_BianchiIX_coreReturnState_transverse_differential
import Theorems.Thm_BianchiIX_core_cone_margin
import Theorems.Thm_BianchiIX_exists_core_cone_threshold
import Theorems.Thm_BianchiIX_exists_large_core_log_derivative_bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreReturnState_multiplier_formula {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hnear : ∀ᶠ Z in 𝓝 Y,
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 2 = 1 ∧
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 1 = Z 1 * coreReturnMultiplier τ Z 0 ∧
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 3 = Z 2 * coreReturnMultiplier τ Z 1)
    (i : Fin 2) :
    (fun Z => coreReturnState τ Z i.succ) =ᶠ[𝓝 Y]
      (fun Z => Z i.succ * coreReturnMultiplier τ Z i) := by
  filter_upwards [hnear] with Z hZ
  fin_cases i
  · exact hZ.2.1
  · change projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 2 *
        projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 3 = _
    rw [hZ.1, one_mul, hZ.2.2]
    rfl

end
end

/-- The actual large-core first return preserves the entrance cone with the margin in (B.41). -/
theorem solution :
    ∃ ε > 0, ε ≤ 1 / 10000 ∧ ∀ Y : CoreAngleState, 6 ≤ Y 0 →
      (0 ≤ Y 1 ∧ Y 1 ≤ ε / Y 0) → (0 ≤ Y 2 ∧ Y 2 ≤ ε / Y 0) →
      ∃ τ : CoreAngleState → ℝ, 0 < τ Y ∧ ContDiffAt ℝ 1 τ Y ∧
        ContDiffAt ℝ 1 (coreReturnState τ) Y ∧
        (∀ᶠ Z in 𝓝 Y,
          IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Z) 0 t 2 = 1} (τ Z) ∧
          projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 1 = Z 1 * coreReturnMultiplier τ Z 0 ∧
          projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 3 = Z 2 * coreReturnMultiplier τ Z 1) ∧
        ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
          let W := fderiv ℝ (coreReturnState τ) Y v
          0 < W 0 ∧ |W 0 - 1| ≤ 1 / (32 * Y 0) ∧
            |W 1| ≤ (1 - 1 / (16 * Y 0)) * Real.sqrt (coreReturnState τ Y 1) * W 0 ∧
            |W 2| ≤ (1 - 1 / (16 * Y 0)) * Real.sqrt (coreReturnState τ Y 2) * W 0 := by
  let R := 1040 + 512 * coreVariationBound
  let A := 20 * coreVariationBound + 4
  let B := 118 * coreVariationBound + 8
  have hK : 0 ≤ coreVariationBound := (Real.exp_pos _).le
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨ε, hε, hεη, hsmallR, hsmallU, hsmallW⟩ := exists_core_cone_threshold hR hA hB
  refine ⟨ε, hε, hεη, ?_⟩
  intro Y hk hu hw
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hu' : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0 :=
    ⟨hu.1, hu.2.trans (div_le_div_of_nonneg_right hεη hk0.le)⟩
  have hw' : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0 :=
    ⟨hw.1, hw.2.trans (div_le_div_of_nonneg_right hεη hk0.le)⟩
  obtain ⟨τ, hτ, hcτ, hnear, hmul, hlogs⟩ := exists_large_core_log_derivative_bounds hk hu' hw'
  obtain ⟨hcF, hrad⟩ := coreReturnState_radius_bound hk hu' hw' (hnear.mono fun _ h => h.1)
  have hhit : ∀ᶠ Z in 𝓝 Y,
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 2 = 1 ∧
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 1 = Z 1 * coreReturnMultiplier τ Z 0 ∧
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 3 = Z 2 * coreReturnMultiplier τ Z 1 :=
    hnear.mono fun _ h => ⟨h.1.1.2, h.2⟩
  have hcon := coreReturnMultiplier_contraction hk hu' hw' hnear.self_of_nhds.1
  have hvalueU : coreReturnState τ Y 1 = Y 1 * coreReturnMultiplier τ Y 0 :=
    (coreReturnState_multiplier_formula hhit 0).self_of_nhds
  have hvalueW : coreReturnState τ Y 2 = Y 2 * coreReturnMultiplier τ Y 1 :=
    (coreReturnState_multiplier_formula hhit 1).self_of_nhds
  refine ⟨τ, hτ, hcτ, hcF, hnear, ?_⟩
  intro v hv0 hv1 hv2 W
  have hd (i : Fin 2) := coreReturnState_transverse_differential
    (hcF.differentiableAt (by norm_num)) hhit i ((hmul i).2.1.differentiableAt (by norm_num)) v
  have hrad' := hrad v
  have hlogs' := hlogs v
  dsimp only at hrad' hlogs'
  rw [hv0, abs_one] at hrad' hlogs'
  have H := core_cone_margin hk ⟨hε.le, by linarith only [hεη]⟩ hu hw hv1 hv2 hR hA hB
    hsmallR hsmallU hsmallW ⟨(hmul 0).1, hcon.1⟩ ⟨(hmul 1).1, hcon.2⟩
    hrad' hlogs'.1 hlogs'.2 (hd 0) (hd 1)
  change 0 < W 0 ∧ |W 0 - 1| ≤ 1 / (32 * Y 0) ∧
    |W 1| ≤ (1 - 1 / (16 * Y 0)) * Real.sqrt (Y 1 * coreReturnMultiplier τ Y 0) * W 0 ∧
    |W 2| ≤ (1 - 1 / (16 * Y 0)) * Real.sqrt (Y 2 * coreReturnMultiplier τ Y 1) * W 0 at H
  rwa [← hvalueU, ← hvalueW] at H
