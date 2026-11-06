-- Prove2me | solution 1 for BianchiIX.exists_coreRadiusReturn_invariant_cone
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:59:18.578867+00:00
-- url     : https://prove2.me/submissions/0c4f9945-221d-48ec-b9f7-75bb1316383e

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreMultiplierDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Theorems.Thm_BianchiIX_coreRadiusReturn_large_regular
import Theorems.Thm_BianchiIX_exists_compact_core_cone
import Theorems.Thm_BianchiIX_exists_large_core_invariant_cone
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
open Set Filter
open scoped Topology


/-- Square-root tangent cones are preserved by the same actual first return at every core radius. -/
theorem solution :
    ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∀ Y : CoreAngleState,
      2 ≤ Y 0 → (0 ≤ Y 1 ∧ Y 1 ≤ ε / Y 0) → (0 ≤ Y 2 ∧ Y 2 ≤ ε / Y 0) →
      ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
        let F := coreReturnState coreRadiusReturnTime
        let d := fderiv ℝ F Y v
        0 < d 0 ∧ ∀ i : Fin 2, |d i.succ| ≤ Real.sqrt (F Y i.succ) * d 0 := by
  obtain ⟨εc, hεc, σ, _, hσ, Hc⟩ := exists_compact_core_cone
  obtain ⟨εl, hεl, hεη, Hl⟩ := exists_large_core_invariant_cone
  refine ⟨min εc εl, lt_min hεc hεl, (min_le_right _ _).trans hεη, ?_⟩
  intro Y hk hu hw v hv0 hv1 hv2 F d
  have hk0 : 0 < Y 0 := by linarith only [hk]
  by_cases hk6 : 6 ≤ Y 0
  · have hsmall := div_le_div_of_nonneg_right (min_le_right εc εl) hk0.le
    have hu' : 0 ≤ Y 1 ∧ Y 1 ≤ εl / Y 0 := ⟨hu.1, hu.2.trans hsmall⟩
    have hw' : 0 ≤ Y 2 ∧ Y 2 ≤ εl / Y 0 := ⟨hw.1, hw.2.trans hsmall⟩
    obtain ⟨τ, _, _, _, hnear, Hcone⟩ := Hl Y hk6 hu' hw'
    have hη := div_le_div_of_nonneg_right hεη hk0.le
    have hcanonical := (coreRadiusReturn_large_regular hk6
      ⟨hu'.1, hu'.2.trans hη⟩ ⟨hw'.1, hw'.2.trans hη⟩).2.2.2
    have htime : coreRadiusReturnTime =ᶠ[𝓝 Y] τ := by
      filter_upwards [hcanonical, hnear] with Z hc ht
      exact hc.unique ht.1
    have hstate : F =ᶠ[𝓝 Y] coreReturnState τ := by
      filter_upwards [htime] with Z hZ
      simp only [F, coreReturnState, hZ]
    obtain ⟨hpos, _, hc1, hc2⟩ := Hcone v hv0 hv1 hv2
    have hderiv : d = fderiv ℝ (coreReturnState τ) Y v := by
      dsimp only [d]
      rw [hstate.fderiv_eq]
    rw [hderiv]
    refine ⟨hpos, ?_⟩
    intro i
    rw [hstate.self_of_nhds]
    have hc : |fderiv ℝ (coreReturnState τ) Y v i.succ| ≤
        (1 - 1 / (16 * Y 0)) * Real.sqrt (coreReturnState τ Y i.succ) *
          fderiv ℝ (coreReturnState τ) Y v 0 := by
      fin_cases i
      · exact hc1
      · exact hc2
    apply hc.trans
    have hfactor : 1 - 1 / (16 * Y 0) ≤ 1 := by
      have hnonneg : 0 ≤ 1 / (16 * Y 0) := by positivity
      linarith only [hnonneg]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hfactor (Real.sqrt_nonneg _)) hpos.le
  · have hsmall : min εc εl / Y 0 ≤ εc :=
      (div_le_self (le_of_lt (lt_min hεc hεl)) (by linarith only [hk])).trans
        (min_le_left _ _)
    obtain ⟨_, _, Hcone⟩ := Hc Y ⟨hk, le_of_not_ge hk6⟩
      ⟨hu.1, hu.2.trans hsmall⟩ ⟨hw.1, hw.2.trans hsmall⟩
    obtain ⟨hpos, hc⟩ := Hcone v hv0 hv1 hv2
    refine ⟨hpos, fun i => (hc i).trans ?_⟩
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hσ.le (Real.sqrt_nonneg _)) hpos.le
