-- Prove2me | solution 1 for BianchiIX.exists_compact_connection_phase_cone_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T17:38:52.133201+00:00
-- url     : https://prove2.me/submissions/0d28a644-8f63-4bcb-8b86-b0ca905776bf

import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Definitions.Def_BianchiIX_Dynamics_CompactConnectionReturn
import Definitions.Def_BianchiIX_EntrancePhaseResponseData
import Theorems.Thm_BianchiIX_compact_phase_cone_direction
import Theorems.Thm_BianchiIX_exists_compact_connection_phase_bounds
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
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
open BianchiIX



theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 10000 ∧ ∀ η : ℝ, (0 < η ∧ η ≤ δ) →
      ∃ ε > (0 : ℝ), ε ≤ 1 / 2 ∧ ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → (0 < Y 1 ∧ Y 1 ≤ ε) → (0 < Y 2 ∧ Y 2 ≤ ε) →
      ContDiffAt ℝ 2 (compactConnectionPhase η) Y ∧
        ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
        1 / 2 ≤ fderiv ℝ (compactConnectionPhase η) Y v ∧
        |fderiv ℝ (compactConnectionPhase η) Y v - 1| ≤ C * (Real.sqrt (Y 1) + Y 2 * Real.sqrt (Y 2)) := by
  obtain ⟨δ, hδ, hδsmall, HP⟩ := exists_compact_connection_phase_bounds
  refine ⟨δ, hδ, hδsmall, ?_⟩
  intro η hη
  obtain ⟨εp, hεp, P, hP, HP'⟩ := HP η hη
  let C := 4 * P + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  let a := 1 / (4 * C)
  have ha : 0 < a := by dsimp only [a]; positivity
  have habudget : 2 * C * a = 1 / 2 := by dsimp only [a]; field_simp; norm_num
  let ε := min εp (min (1 / 2) (a ^ 2))
  have hεp' : ε ≤ εp := min_le_left _ _
  have hεhalf : ε ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hεroot : Real.sqrt ε ≤ a := Real.sqrt_le_iff.mpr
    ⟨ha.le, (min_le_right _ _).trans (min_le_right _ _)⟩
  refine ⟨ε, lt_min hεp (lt_min (by norm_num) (sq_pos_of_pos ha)), hεhalf, C, hC, ?_⟩
  intro Y hk hu hw
  obtain ⟨_, _, hphase, _, Hr, Ht⟩ := HP' Y hk ⟨hu.1, hu.2.trans hεp'⟩ ⟨hw.1, hw.2.trans hεp'⟩
  have hu1 : Y 1 ≤ 1 := by linarith only [hu.2, hεhalf]
  have hw1 : Y 2 ≤ 1 := by linarith only [hw.2, hεhalf]
  refine ⟨hphase, ?_⟩
  intro v hv0 hv1 hv2
  have H := compact_phase_cone_direction (fderiv ℝ (compactConnectionPhase η) Y) v hP.le
    (by linarith only [hk.1]) ⟨hu.1.le, hu1⟩ ⟨hw.1.le, hw1⟩ hv0 hv1 hv2 Hr Ht
  change |fderiv ℝ (compactConnectionPhase η) Y v - 1| ≤ C * (Real.sqrt (Y 1) + Y 2 * Real.sqrt (Y 2)) at H
  have hsize : Real.sqrt (Y 1) + Y 2 * Real.sqrt (Y 2) ≤ 2 * a := by
    have hsu := (Real.sqrt_le_sqrt hu.2).trans hεroot
    have hsw := (Real.sqrt_le_sqrt hw.2).trans hεroot
    have H' := mul_le_mul_of_nonneg_right hw1 (Real.sqrt_nonneg (Y 2))
    linarith only [hsu, hsw, H']
  have Hsmall := H.trans (mul_le_mul_of_nonneg_left hsize hC.le)
  have Hsmall' : |fderiv ℝ (compactConnectionPhase η) Y v - 1| ≤ 1 / 2 := by
    nlinarith only [Hsmall, habudget]
  exact ⟨by linarith only [(abs_le.mp Hsmall').1], H⟩
