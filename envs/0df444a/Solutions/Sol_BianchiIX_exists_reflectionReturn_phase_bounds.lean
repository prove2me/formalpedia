-- Prove2me | solution 1 for BianchiIX.exists_reflectionReturn_phase_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:34:16.921233+00:00
-- url     : https://prove2.me/submissions/f4321771-dc8b-413b-83e3-4f80a67b67e2

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_EraReturnData
import Theorems.Thm_BianchiIX_exists_compact_reflection_estimates
import Theorems.Thm_BianchiIX_exists_long_reflection_estimates
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Module
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open BianchiIX
open Set



/-- Compact and long estimates apply to one canonical reflection map on a common amplitude domain. -/
theorem solution :
    ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      31 / 8 ≤ Y 0 → (0 < Y 1 ∧ Y 1 ≤ ε / Y 0) → (0 < Y 2 ∧ Y 2 ≤ ε / Y 0) →
      IsLeast {t : ℝ | 0 < t ∧ projectiveOriginalFlow (coreTailEntry Y) 0 t 3 = 1}
        (reflectionReturnTime Y) ∧
      coreRadiusEntry (reflectionReturnState Y) =
        projectiveReflection (projectiveOriginalFlow (coreTailEntry Y) 0 (reflectionReturnTime Y)) ∧
      ContDiffAt ℝ 2 reflectionReturnTime Y ∧ ContDiffAt ℝ 2 reflectionReturnState Y ∧
      |reflectionReturnState Y 0 - (Y 0 - 2)| ≤ C * (Y 1 + Y 2) / Y 0 ∧
      (∀ i : Fin 2, 0 < reflectionReturnState Y i.succ ∧ reflectionReturnState Y i.succ ≤ Y i.succ) ∧
      ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
        let d := fderiv ℝ reflectionReturnState Y v
        1 / 2 ≤ d 0 ∧ |d 0 - 1| ≤ C * Real.sqrt (Y 1 + Y 2) / Y 0 ∧
          ∀ i : Fin 2, |d i.succ| ≤ Real.sqrt (reflectionReturnState Y i.succ) * d 0 := by
  obtain ⟨εc, hεc, Cc, hCc, HC⟩ := exists_compact_reflection_estimates
  obtain ⟨εl, hεl, hεmax, HL⟩ := exists_long_reflection_estimates
  let C := max Cc 300000
  refine ⟨min εc εl, lt_min hεc hεl, (min_le_right _ _).trans hεmax,
    C, lt_of_lt_of_le hCc (le_max_left _ _), ?_⟩
  intro Y hR hu hw
  have hR0 : 0 < Y 0 := by linarith only [hR]
  have hb : 0 ≤ Y 1 + Y 2 := add_nonneg hu.1.le hw.1.le
  have hscale {K : ℝ} (hK : K ≤ C) {b : ℝ} (hb : 0 ≤ b) : K * b / Y 0 ≤ C * b / Y 0 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hK hb) hR0.le
  by_cases hlong : 11 / 2 ≤ Y 0
  · have hsmall := div_le_div_of_nonneg_right (min_le_right εc εl) hR0.le
    obtain ⟨hfirst, hactual, ht, hF, hval, hwalls, hderiv⟩ := HL Y hlong
      ⟨hu.1, hu.2.trans hsmall⟩ ⟨hw.1, hw.2.trans hsmall⟩
    refine ⟨hfirst, hactual, ht, hF, hval.trans (hscale (le_max_right _ _) hb), hwalls, ?_⟩
    intro v hv0 hv1 hv2
    obtain ⟨hmargin, herr, hcone⟩ := hderiv v hv0 hv1 hv2
    exact ⟨hmargin, herr.trans (hscale (le_max_right _ _) (Real.sqrt_nonneg _)), hcone⟩
  · have hsmall : min εc εl / Y 0 ≤ εc :=
      (div_le_self (lt_min hεc hεl).le (by linarith only [hR])).trans (min_le_left _ _)
    obtain ⟨hfirst, hactual, ht, hF, hval, hwalls, hderiv⟩ := HC Y
      ⟨hR, by linarith only [lt_of_not_ge hlong]⟩ ⟨hu.1, hu.2.trans hsmall⟩ ⟨hw.1, hw.2.trans hsmall⟩
    refine ⟨hfirst, hactual, ht, hF, hval.trans (hscale (le_max_left _ _) hb), hwalls, ?_⟩
    intro v hv0 hv1 hv2
    obtain ⟨hmargin, herr, hcone⟩ := hderiv v hv0 hv1 hv2
    exact ⟨hmargin, herr.trans (hscale (le_max_left _ _) (Real.sqrt_nonneg _)), hcone⟩
