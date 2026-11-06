-- Prove2me | solution 1 for BianchiIX.exists_arbitrarily_late_compact_core
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:16:23.795454+00:00
-- url     : https://prove2.me/submissions/7df688b1-51a6-4a03-8654-f2801f978bc3

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_GeometricExceptionData
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Theorems.Thm_BianchiIX_exists_late_compact_core
import Theorems.Thm_BianchiIX_normalizedMaxCurve_restart
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_normalized_positive_walls_invariant
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
open Set Filter
open scoped Topology

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


/-- Eventual product smallness gives compact small cores after every prescribed original time. -/
theorem solution {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ γ > (0 : ℝ), γ < 1 / 4 ∧ ∀ B : ℝ, 0 < B →
      ∀ x : NormalizedState, stateConstraint x = 1 → positiveWalls x →
        (∀ᶠ t in atTop, ∀ i, ε ≤ normalizedEuclideanDistance (normalizedMaxCurve x 0 t) (taubPoint i)) →
        (∀ Δ : ℝ, 0 < Δ → ∀ᶠ t in atTop, normalizedWallProductsBound Δ (normalizedMaxCurve x 0 t)) →
        ∀ r : ℝ, ∃ T > max r 0, ∃ a : Fin 6, ∃ Y : CoreAngleState,
          T ∈ normalizedMaxDomain x 0 ∧
          fromProjectiveState (coreRadiusEntry Y) = (axisFrame a).map (normalizedMaxCurve x 0 T) ∧
          Y ∈ compactEraPhase N γ ∧ 0 < Y 1 ∧ 0 < Y 2 ∧ Y 1 + Y 2 ≤ B ∧
          normalizedTaubAvoidance ε (fromProjectiveState (coreRadiusEntry Y)) ∧
          0 < fderiv ℝ projectiveActiveWall (fromProjectiveState (coreRadiusEntry Y))
            (normalizedField (fromProjectiveState (coreRadiusEntry Y))) := by
  obtain ⟨N, γ, hγ, hγmax, H⟩ := exists_late_compact_core hε
  refine ⟨N, γ, hγ, hγmax, ?_⟩
  intro B hB x hc hp ha hprod r
  obtain ⟨Δ, hΔ, HΔ⟩ := H B hB
  obtain ⟨R, hR⟩ := eventually_atTop.mp ((hprod Δ hΔ).and ha)
  let s := max 0 (max r R)
  have hs : 0 ≤ s := le_max_left _ _
  have hsr : r ≤ s := (le_max_left _ _).trans (le_max_right _ _)
  have hsR : R ≤ s := (le_max_right _ _).trans (le_max_right _ _)
  have hdoms := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs
  let y := normalizedMaxCurve x 0 s
  have hcy : stateConstraint y = 1 := (normalizedMaxCurve_constraint hdoms).trans hc
  have hpy : positiveWalls y := normalized_positive_walls_invariant
    (convex_normalizedMaxDomain x 0) (isOpen_normalizedMaxDomain x 0)
    (fun _ ht => hasDerivAt_normalizedMaxCurve ht) (initial_mem_normalizedMaxDomain x 0)
    hdoms (by simpa only [normalizedMaxCurve_initial] using hp)
  have hshift (u : ℝ) (hu : 0 ≤ u) :
      normalizedMaxCurve x 0 (s + u) = normalizedMaxCurve y 0 u := by
    have Hs := (normalizedMaxCurve_restart (t := s + u) hdoms (by
      simpa only [add_sub_cancel_left] using normalizedMaxDomain_contains_Ici_of_constraint hcy 0 hu)).2
    simpa only [add_sub_cancel_left] using Hs
  have hprody (u : ℝ) (hu : 0 ≤ u) : normalizedWallProductsBound Δ (normalizedMaxCurve y 0 u) := by
    rw [← hshift u hu]
    exact (hR (s + u) (hsR.trans (le_add_of_nonneg_right hu))).1
  have hay : normalizedTaubAvoidance ε y := by
    intro u hu _ i
    rw [← hshift u hu]
    exact (hR (s + u) (hsR.trans (le_add_of_nonneg_right hu))).2 i
  obtain ⟨τ, hτ, a, Y, _, heq, hphase, hU, hW, hsum, havoid, htrans⟩ :=
    HΔ Δ ⟨hΔ.le, le_rfl⟩ y hcy hpy hay hprody
  have hT : max r 0 < s + τ := max_lt_iff.mpr
    ⟨by linarith only [hsr, hτ], by linarith only [hs, hτ]⟩
  refine ⟨s + τ, hT, a, Y,
    normalizedMaxDomain_contains_Ici_of_constraint hc 0 (add_nonneg hs hτ.le),
    ?_, hphase, hU, hW, hsum, havoid, htrans⟩
  rw [hshift τ hτ.le]
  exact heq
