-- Prove2me | solution 1 for BianchiIX.exists_coreRadiusReturn_phase_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:53:57.432216+00:00
-- url     : https://prove2.me/submissions/043ee301-3b66-46f4-8964-a434fe22fab6

import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Theorems.Thm_BianchiIX_coreRadiusReturn_large_phase_value
import Theorems.Thm_BianchiIX_coreRadiusReturn_large_regular
import Theorems.Thm_BianchiIX_coreReturnState_radius_cone_bound
import Theorems.Thm_BianchiIX_exists_compact_core_phase_bounds
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

noncomputable section
open BianchiIX
open Set


/-- A single first-return map has amplitude-dependent phase and ordinary derivative errors for all radii. -/
theorem solution :
    ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      2 ≤ Y 0 → (0 ≤ Y 1 ∧ Y 1 ≤ ε / Y 0) → (0 ≤ Y 2 ∧ Y 2 ≤ ε / Y 0) →
      let F := coreReturnState coreRadiusReturnTime
      coreRadiusReturnValid Y ∧ ContDiffAt ℝ 1 F Y ∧
        |F Y 0 - Y 0| ≤ C * (Y 1 + Y 2) / Y 0 ∧
        ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
          |fderiv ℝ F Y v 0 - 1| ≤ C * Real.sqrt (Y 1 + Y 2) / Y 0 := by
  obtain ⟨ε, hε, C, hC, H⟩ := exists_compact_core_phase_bounds
  let B := 5 * (1040 + 512 * coreVariationBound)
  let C' := max 16 (max C B)
  have hCC : C ≤ C' := (le_max_left _ _).trans (le_max_right _ _)
  have hBC : B ≤ C' := (le_max_right _ _).trans (le_max_right _ _)
  have h16C : 16 ≤ C' := le_max_left _ _
  refine ⟨min ε (1 / 10000), lt_min hε (by norm_num), min_le_right _ _,
    C', lt_of_lt_of_le hC hCC, ?_⟩
  intro Y hk hu hw F
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hb : 0 ≤ Y 1 + Y 2 := add_nonneg hu.1 hw.1
  have hη : min ε (1 / 10000) / Y 0 ≤ (1 / 10000) / Y 0 :=
    div_le_div_of_nonneg_right (min_le_right _ _) hk0.le
  by_cases hk6 : 6 ≤ Y 0
  · have hu' := And.intro hu.1 (hu.2.trans hη)
    have hw' := And.intro hw.1 (hw.2.trans hη)
    obtain ⟨hvalid, _, hF, hnear⟩ := coreRadiusReturn_large_regular hk6 hu' hw'
    refine ⟨hvalid, hF, (coreRadiusReturn_large_phase_value hk6 hu' hw').trans ?_, ?_⟩
    · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h16C hb) hk0.le
    · intro v hv0 hv1 hv2
      exact (coreReturnState_radius_cone_bound hk6 hu' hw' hnear v hv0 hv1 hv2).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBC (Real.sqrt_nonneg _)) hk0.le)
  · have hsmall : min ε (1 / 10000) / Y 0 ≤ ε :=
      (div_le_self (le_of_lt (lt_min hε (by norm_num))) (by linarith only [hk])).trans
        (min_le_left _ _)
    obtain ⟨hvalid, hF, hvalue, hderiv⟩ := H Y ⟨hk, le_of_not_ge hk6⟩
      ⟨hu.1, hu.2.trans hsmall⟩ ⟨hw.1, hw.2.trans hsmall⟩
    refine ⟨hvalid, hF.of_le (by norm_num), hvalue.trans ?_, ?_⟩
    · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hb) hk0.le
    · intro v hv0 hv1 hv2
      exact (hderiv v hv0 hv1 hv2).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCC (Real.sqrt_nonneg _)) hk0.le)
