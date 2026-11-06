-- Prove2me | solution 1 for BianchiIX.coreReturnState_radius_cone_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:33:10.607208+00:00
-- url     : https://prove2.me/submissions/e17b8a0c-6d66-46e8-a348-6e2b6e94bde6

import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Theorems.Thm_BianchiIX_coreReturnState_radius_bound
import Theorems.Thm_BianchiIX_core_cone_radius_size
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


/-- Formula (B.40) keeps the actual entrance wall sum. -/
theorem solution {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hk : 6 ≤ Y 0) (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0)
    (hnear : ∀ᶠ Z in 𝓝 Y, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Z) 0 t 2 = 1} (τ Z))
    (v : CoreAngleState) (hv0 : v 0 = 1) (hv1 : |v 1| ≤ Real.sqrt (Y 1)) (hv2 : |v 2| ≤ Real.sqrt (Y 2)) :
    |(fderiv ℝ (coreReturnState τ) Y v) 0 - 1| ≤
      (5 * (1040 + 512 * coreVariationBound)) * Real.sqrt (Y 1 + Y 2) / Y 0 := by
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hR : 0 ≤ 1040 + 512 * coreVariationBound := by
    have hK := (Real.exp_pos (2 * Real.pi + 48 / 10000)).le
    change 0 ≤ coreVariationBound at hK
    positivity
  have H := (coreReturnState_radius_bound hk hu hw hnear).2 v
  rw [hv0, abs_one] at H
  have hsize := core_cone_radius_size hk
    (by norm_num : (0 : ℝ) ≤ 1 / 10000 ∧ (1 : ℝ) / 10000 ≤ 1) hu hw hv1 hv2
  apply H.trans
  calc
    _ = (1040 + 512 * coreVariationBound) *
        (|v 1| + (Y 1 + Y 2) * (1 + Y 0 * |v 1| + |v 2|)) / Y 0 := by ring
    _ ≤ (1040 + 512 * coreVariationBound) * (5 * Real.sqrt (Y 1 + Y 2)) / Y 0 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith only [hv1, hsize]) hR) hk0.le
    _ = _ := by ring
