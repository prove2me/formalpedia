-- Prove2me | solution 1 for BianchiIX.exists_late_compact_core
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:14:45.887203+00:00
-- url     : https://prove2.me/submissions/39584e43-5e76-4659-b753-e445436972ef

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_GeometricExceptionData
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Theorems.Thm_BianchiIX_exists_compactEraPhase_of_taub_avoidance
import Theorems.Thm_BianchiIX_exists_late_physical_core
import Theorems.Thm_BianchiIX_fromProjectiveState_toProjectiveState
import Theorems.Thm_BianchiIX_normalized_constraint_constant
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
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
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.List.Induction
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Floor

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalizedMaxCurve_constraint {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    stateConstraint (normalizedMaxCurve x t₀ t) = stateConstraint x := by
  simpa only [normalizedMaxCurve_initial] using
    normalized_constraint_constant (convex_normalizedMaxDomain x t₀)
      (fun _ hu => hasDerivAt_normalizedMaxCurve hu) (initial_mem_normalizedMaxDomain x t₀) ht

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.referenceCoreWallFloor_pos (K : ℝ) : 0 < referenceCoreWallFloor K := by
  unfold referenceCoreWallFloor
  positivity

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRadiusEntry_of_upward_section {y : ProjectiveState}
    (hm : 1 ≤ y 0) (hv : y 2 = 1) :
    coreRadiusEntry (toCoreAngleState y) = y := by
  have he : coreEnergy (y 0) (y 2) = (y 0 - 1) ^ 2 + 1 := by
    simp only [coreEnergy, hv, one_pow]
  have hs : coreRadius (y 0) (y 2) ^ 2 - 1 = (y 0 - 1) ^ 2 := by
    rw [coreRadius, Real.sq_sqrt (by rw [he]; positivity), he]
    ring
  ext i
  fin_cases i
  · change 1 + Real.sqrt (coreRadius (y 0) (y 2) ^ 2 - 1) = y 0
    rw [hs, Real.sqrt_sq (sub_nonneg.mpr hm)]
    ring
  · rfl
  · exact hv.symm
  · change y 2 * y 3 = y 3
    rw [hv, one_mul]

end
end


/-- A common late product threshold produces an arbitrarily small core in a compact phase range. -/
theorem solution {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ γ > (0 : ℝ), γ < 1 / 4 ∧ ∀ B : ℝ, 0 < B →
      ∃ Δ₀ > (0 : ℝ), ∀ Δ ∈ Icc 0 Δ₀,
        ∀ x : NormalizedState, stateConstraint x = 1 → positiveWalls x →
          normalizedTaubAvoidance ε x →
          (∀ u ≥ (0 : ℝ), normalizedWallProductsBound Δ (normalizedMaxCurve x 0 u)) →
          ∃ T > (0 : ℝ), ∃ a : Fin 6, ∃ Y : CoreAngleState,
            T ∈ normalizedMaxDomain x 0 ∧
            fromProjectiveState (coreRadiusEntry Y) = (axisFrame a).map (normalizedMaxCurve x 0 T) ∧
            Y ∈ compactEraPhase N γ ∧ 0 < Y 1 ∧ 0 < Y 2 ∧ Y 1 + Y 2 ≤ B ∧
            normalizedTaubAvoidance ε (fromProjectiveState (coreRadiusEntry Y)) ∧
            0 < fderiv ℝ projectiveActiveWall (fromProjectiveState (coreRadiusEntry Y))
              (normalizedField (fromProjectiveState (coreRadiusEntry Y))) := by
  obtain ⟨N, γ, hγ, hγmax, B₀, hB₀, Hphase⟩ := exists_compactEraPhase_of_taub_avoidance hε
  obtain ⟨Δ₁, hΔ₁, C, hC, Hcore⟩ := exists_late_physical_core hε
  have hCpos : 0 < C := by linarith only [hC]
  let n := referenceCoreWallFloor (8 / ε)
  have hn : 0 < n := referenceCoreWallFloor_pos _
  refine ⟨N, γ, hγ, hγmax, ?_⟩
  intro B hB
  let b := min B B₀
  have hb : 0 < b := lt_min hB hB₀
  let Δ₀ := min Δ₁ (min 1 (min (γ / (2 * C)) (2 * b * n ^ 2)))
  have hΔ₀ : 0 < Δ₀ := by dsimp [Δ₀]; positivity
  refine ⟨Δ₀, hΔ₀, ?_⟩
  intro Δ hΔ x hc hp ha hprod
  have hΔC : Δ ≤ Δ₁ := hΔ.2.trans (min_le_left _ _)
  have hΔ1 : Δ ≤ 1 := hΔ.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hΔγ : Δ ≤ γ / (2 * C) := hΔ.2.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hΔb : Δ ≤ 2 * b * n ^ 2 := hΔ.2.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hsq : Δ ^ 2 ≤ Δ := by nlinarith only [hΔ.1, hΔ1]
  have herror : C * Δ ^ 2 ≤ γ / 2 := by
    have H := (le_div_iff₀ (by positivity : 0 < 2 * C)).mp hΔγ
    have Hsq := mul_le_mul_of_nonneg_left hsq hCpos.le
    nlinarith only [H, Hsq]
  have hamp : Δ ^ 2 / (2 * n ^ 2) ≤ b := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * n ^ 2)).mpr
    nlinarith only [hsq, hΔb]
  obtain ⟨s, hs, T, hTs, a, k, hk, _, _, hdom, _, hV, hM, hA, hphase,
    _, hU, hW, hweak, htrans, havoid⟩ := Hcore Δ ⟨hΔ.1, hΔC⟩ x hc hp ha hprod
  let X := (axisFrame a).map (normalizedMaxCurve x 0 T)
  let y := toProjectiveState X
  let Y : CoreAngleState := ![coreRadius (y 0) (y 2), y 1, y 3]
  have hlow : 2 - γ / 2 ≤ Y 0 := by
    have Hlo := (abs_le.mp hphase).1
    change 2 - γ / 2 ≤ coreRadius (y 0) (y 2)
    change -(C * Δ ^ 2) ≤ coreRadius (y 0) (y 2) - k at Hlo
    linarith only [Hlo, hk, herror]
  have hsum : Y 1 + Y 2 ≤ b := hweak.trans hamp
  have hcX : stateConstraint X = 1 := ((axisFrame a).constraint _).trans
    ((normalizedMaxCurve_constraint hdom).trans hc)
  have hcoords : toCoreAngleState y = Y := by
    change y 2 = 1 at hV
    simp only [toCoreAngleState, hV, one_mul, Y]
  have hentry : coreRadiusEntry Y = y := by
    rw [← hcoords]
    exact coreRadiusEntry_of_upward_section hM.le hV
  have hphysical : fromProjectiveState (coreRadiusEntry Y) = X := by
    rw [hentry]
    exact fromProjectiveState_toProjectiveState hA.ne' hcX
  have havoidY : normalizedTaubAvoidance ε (fromProjectiveState (coreRadiusEntry Y)) := by
    rw [hphysical]
    exact havoid
  refine ⟨T, hs.trans hTs, a, Y, hdom, hphysical,
    Hphase Y hlow hU hW (hsum.trans (min_le_right _ _)) havoidY,
    hU, hW, hsum.trans (min_le_left _ _), havoidY, ?_⟩
  rwa [hphysical]
