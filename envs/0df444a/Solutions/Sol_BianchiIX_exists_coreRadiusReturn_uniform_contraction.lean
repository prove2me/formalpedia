-- Prove2me | solution 1 for BianchiIX.exists_coreRadiusReturn_uniform_contraction
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T04:47:40.50137+00:00
-- url     : https://prove2.me/submissions/206b0991-4d2c-4126-82f8-5d0f7e626b14

import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Definitions.Def_BianchiIX_Dynamics_CompactCoreFactors
import Theorems.Thm_BianchiIX_coreRadiusReturn_large_regular
import Theorems.Thm_BianchiIX_coreRadiusReturn_large_walls
import Theorems.Thm_BianchiIX_exists_compact_core_factor_bounds
import Theorems.Thm_BianchiIX_exists_compact_core_return_two_germ
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
import Mathlib.Analysis.Calculus.Deriv.Pi

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.exists_compact_core_return_two :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (2 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      coreRadiusReturnValid Y ∧ ContDiffAt ℝ 2 coreRadiusReturnTime Y ∧
        ContDiffAt ℝ 2 (coreReturnState coreRadiusReturnTime) Y ∧
        ‖fderiv ℝ coreRadiusReturnTime Y‖ +
          ‖fderiv ℝ (coreReturnState coreRadiusReturnTime) Y‖ +
          ‖fderiv ℝ (fderiv ℝ coreRadiusReturnTime) Y‖ +
          ‖fderiv ℝ (fderiv ℝ (coreReturnState coreRadiusReturnTime)) Y‖ ≤ C := by
  obtain ⟨ε, hε, C, hC, h⟩ := exists_compact_core_return_two_germ
  refine ⟨ε, hε, C, hC, ?_⟩
  intro Y hk hu hw
  have H := h Y hk hu hw
  exact ⟨H.1, H.2.1, H.2.2.1, H.2.2.2.1⟩

end
end

/-- One actual first-return map and one exponential loss rate apply to every core radius at least two. -/
theorem solution :
    ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ c > (0 : ℝ), c ≤ 1 / 2 ∧
      ∀ Y : CoreAngleState, 2 ≤ Y 0 →
        (0 ≤ Y 1 ∧ Y 1 ≤ ε / Y 0) → (0 ≤ Y 2 ∧ Y 2 ≤ ε / Y 0) →
        coreRadiusReturnValid Y ∧ ContDiffAt ℝ 1 coreRadiusReturnTime Y ∧
          ContDiffAt ℝ 1 (coreReturnState coreRadiusReturnTime) Y ∧
          ∀ i : Fin 2, 0 ≤ coreReturnState coreRadiusReturnTime Y i.succ ∧
            (0 < coreReturnState coreRadiusReturnTime Y i.succ ↔ 0 < Y i.succ) ∧
            coreReturnState coreRadiusReturnTime Y i.succ ≤ Real.exp (-c / Y 0) * Y i.succ := by
  obtain ⟨εf, hεf, q, hq, hq1, C, hC, HF⟩ := exists_compact_core_factor_bounds
  obtain ⟨εt, hεt, Ct, hCt, HT⟩ := exists_compact_core_return_two
  let ε := min (1 / 10000) (min εf εt)
  let c := min (1 / 2) (-2 * Real.log q)
  have hlog : Real.log q < 0 := Real.log_neg hq hq1
  have hε : 0 < ε := lt_min (by norm_num) (lt_min hεf hεt)
  have hc : 0 < c := lt_min (by norm_num) (by linarith only [hlog])
  have hcmax : c ≤ 1 / 2 := min_le_left _ _
  have hcq : c ≤ -2 * Real.log q := min_le_right _ _
  refine ⟨ε, hε, min_le_left _ _, c, hc, hcmax, ?_⟩
  intro Y hk hu hw
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hεk : ε / Y 0 ≤ ε := div_le_self hε.le (by linarith only [hk])
  by_cases hk6 : 6 ≤ Y 0
  · have hu' : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0 :=
      ⟨hu.1, hu.2.trans (div_le_div_of_nonneg_right (min_le_left _ _) hk0.le)⟩
    have hw' : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0 :=
      ⟨hw.1, hw.2.trans (div_le_div_of_nonneg_right (min_le_left _ _) hk0.le)⟩
    obtain ⟨hvalid, ht, hF, _⟩ := coreRadiusReturn_large_regular hk6 hu' hw'
    refine ⟨hvalid, ht, hF, ?_⟩
    intro i
    obtain ⟨hpos, hiff, hdec⟩ := coreRadiusReturn_large_walls hk6 hu' hw' i
    have hi : 0 ≤ Y i.succ := by
      fin_cases i
      · exact hu.1
      · exact hw.1
    refine ⟨hpos, hiff, hdec.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hi)⟩
    rw [show -1 / (2 * Y 0) = -(1 / 2) / Y 0 by ring]
    exact div_le_div_of_nonneg_right (by linarith only [hcmax]) hk0.le
  · have hkr : 2 ≤ Y 0 ∧ Y 0 ≤ 6 := ⟨hk, (lt_of_not_ge hk6).le⟩
    have huf : |Y 1| ≤ εf := by
      rw [abs_of_nonneg hu.1]
      exact (hu.2.trans hεk).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hwf : |Y 2| ≤ εf := by
      rw [abs_of_nonneg hw.1]
      exact (hw.2.trans hεk).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hut : |Y 1| ≤ εt := by
      rw [abs_of_nonneg hu.1]
      exact (hu.2.trans hεk).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hwt : |Y 2| ≤ εt := by
      rw [abs_of_nonneg hw.1]
      exact (hw.2.trans hεk).trans ((min_le_right _ _).trans (min_le_right _ _))
    obtain ⟨hvalid, hF, H⟩ := HF Y hkr huf hwf
    refine ⟨hvalid, (HT Y hkr hut hwt).2.1.of_le (by norm_num), hF.of_le (by norm_num), ?_⟩
    have hqe : q ≤ Real.exp (-c / Y 0) := by
      rw [← Real.exp_log hq]
      apply Real.exp_le_exp.mpr
      apply (le_div_iff₀ hk0).mpr
      nlinarith only [mul_le_mul_of_nonpos_right hk hlog.le, hcq]
    intro i
    have hi : 0 ≤ Y i.succ := by
      fin_cases i
      · exact hu.1
      · exact hw.1
    obtain ⟨hformula, hpos, hbound, _⟩ := H i
    rw [hformula]
    exact ⟨mul_nonneg hi hpos.le, mul_pos_iff_of_pos_right hpos,
      (mul_le_mul_of_nonneg_left (hbound.trans hqe) hi).trans_eq (mul_comm _ _)⟩
