-- Prove2me | solution 1 for BianchiIX.exists_compact_connection_cone
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T18:03:22.254591+00:00
-- url     : https://prove2.me/submissions/fcc965d9-0944-417f-b6ff-92ac5b7744ef

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Definitions.Def_BianchiIX_Dynamics_CompactConnectionReturn
import Definitions.Def_BianchiIX_EntrancePhaseResponseData
import Theorems.Thm_BianchiIX_exists_common_rpow_budget
import Theorems.Thm_BianchiIX_exists_compact_connection_phase_cone_bounds
import Theorems.Thm_BianchiIX_exists_compact_connection_weighted_wall_bounds
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



/-- The actual compact connection strictly preserves the square-root cone, uniformly over wall ratios. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 10000 ∧ ∀ η : ℝ, (0 < η ∧ η ≤ δ) →
      ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → (0 < Y 1 ∧ Y 1 ≤ ε) → (0 < Y 2 ∧ Y 2 ≤ ε) →
      coreTailValid η Y ∧ entranceReturnValid (compactConnectionEntry η Y) ∧
        ContDiffAt ℝ 2 (compactConnectionState η) Y ∧ ContDiffAt ℝ 2 (compactConnectionPhase η) Y ∧
        0 < compactConnectionState η Y 1 ∧ 0 < compactConnectionState η Y 3 ∧
        C * (Y 1 + Y 2) ^ (2 / 9 : ℝ) < 1 / 2 ∧
        ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
        let r := fderiv ℝ (compactConnectionPhase η) Y v
        1 / 2 ≤ r ∧ |r - 1| ≤ C * (Real.sqrt (Y 1) + Y 2 * Real.sqrt (Y 2)) ∧
        |fderiv ℝ (compactConnectionState η) Y v 1| ≤
          C * (Y 1 + Y 2) ^ (2 / 9 : ℝ) * Real.sqrt (compactConnectionState η Y 1) * r ∧
        |fderiv ℝ (compactConnectionState η) Y v 3| ≤
          C * (Y 1 + Y 2) ^ (2 / 9 : ℝ) * Real.sqrt (compactConnectionState η Y 3) * r := by
  obtain ⟨δp, hδp, hδpsmall, HP⟩ := exists_compact_connection_phase_cone_bounds
  obtain ⟨δw, hδw, _, HW⟩ := exists_compact_connection_weighted_wall_bounds
  refine ⟨min δp δw, lt_min hδp hδw, (min_le_left _ _).trans hδpsmall, ?_⟩
  intro η hη
  obtain ⟨εp, hεp, hεphalf, P, hP, HP'⟩ := HP η ⟨hη.1, hη.2.trans (min_le_left _ _)⟩
  obtain ⟨εw, hεw, W, hW, HW'⟩ := HW η ⟨hη.1, hη.2.trans (min_le_right _ _)⟩
  let C := 2 * W + P
  have hC : 0 < C := by dsimp only [C]; positivity
  have hPC : P ≤ C := by dsimp only [C]; linarith only [hW]
  have hWC : 2 * W ≤ C := by dsimp only [C]; linarith only [hP]
  obtain ⟨b, hb, hbmax, Hbudget⟩ := exists_common_rpow_budget (ι := Fin 1) Finset.univ
    (C := fun _ => C) (p := fun _ => 2 / 9) (ε := fun _ => 1 / 2)
    (fun _ _ => hC.le) (by intros; norm_num) (by intros; norm_num) (lt_min hεp hεw)
  let ε := b / 2
  have hεb : ε ≤ b := by dsimp only [ε]; linarith only [hb]
  have hεp' : ε ≤ εp := hεb.trans (hbmax.le.trans (min_le_left _ _))
  have hεw' : ε ≤ εw := hεb.trans (hbmax.le.trans (min_le_right _ _))
  refine ⟨ε, half_pos hb, C, hC, ?_⟩
  intro Y hk hu hw
  obtain ⟨hphase, Hphase⟩ := HP' Y hk ⟨hu.1, hu.2.trans hεp'⟩ ⟨hw.1, hw.2.trans hεp'⟩
  obtain ⟨htail, hreturn, hstate, hU, hV, Hwall⟩ := HW' Y hk ⟨hu.1, hu.2.trans hεw'⟩ ⟨hw.1, hw.2.trans hεw'⟩
  have hsum : 0 < Y 1 + Y 2 := add_pos hu.1 hw.1
  have hsumb : Y 1 + Y 2 ≤ b := by dsimp only [ε] at hu hw; linarith only [hu.2, hw.2]
  have hsum1 : Y 1 + Y 2 ≤ 1 := by linarith only [hu.2.trans hεp', hw.2.trans hεp', hεphalf]
  have hpow : (Y 1 + Y 2) ^ (19 / 24 : ℝ) ≤ (Y 1 + Y 2) ^ (2 / 9 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hsum hsum1 (by norm_num)
  refine ⟨htail, hreturn, hstate, hphase, hU, hV, Hbudget _ ⟨hsum, hsumb⟩ 0 (Finset.mem_univ _), ?_⟩
  intro v hv0 hv1 hv2
  obtain ⟨hr, herror⟩ := Hphase v hv0 hv1 hv2
  obtain ⟨hwu, hwv⟩ := Hwall v hv0 hv1 hv2
  have hfactor : W ≤ C * fderiv ℝ (compactConnectionPhase η) Y v := by
    have H := mul_le_mul_of_nonneg_left hr hC.le
    linarith only [H, hWC]
  refine ⟨hr, herror.trans (mul_le_mul_of_nonneg_right hPC (by positivity [hw.1])), ?_, ?_⟩
  · calc
      _ ≤ W * (Y 1 + Y 2) ^ (2 / 9 : ℝ) * Real.sqrt (compactConnectionState η Y 1) :=
        hwu.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hW.le) (Real.sqrt_nonneg _))
      _ ≤ (C * fderiv ℝ (compactConnectionPhase η) Y v) * (Y 1 + Y 2) ^ (2 / 9 : ℝ) *
          Real.sqrt (compactConnectionState η Y 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hsum.le _)) (Real.sqrt_nonneg _)
      _ = _ := by ring
  · calc
      _ ≤ W * (Y 1 + Y 2) ^ (2 / 9 : ℝ) * Real.sqrt (compactConnectionState η Y 3) := hwv
      _ ≤ (C * fderiv ℝ (compactConnectionPhase η) Y v) * (Y 1 + Y 2) ^ (2 / 9 : ℝ) *
          Real.sqrt (compactConnectionState η Y 3) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hsum.le _)) (Real.sqrt_nonneg _)
      _ = _ := by ring
