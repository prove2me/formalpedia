-- Prove2me | solution 1 for BianchiIX.exists_large_core_projected_growth
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:47:56.472873+00:00
-- url     : https://prove2.me/submissions/9c59b40f-b110-4496-bffc-b80b25356717

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreWeightedVariation
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreProjectedFlowVariation_growth
import Theorems.Thm_BianchiIX_exists_large_core_traversal
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_projective_chart_differential_inverse
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
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

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.normalizedFlowDifferential_initial (x : NormalizedState) (t₀ : ℝ) :
    normalizedFlowDifferential x t₀ t₀ = ContinuousLinearMap.id ℝ NormalizedState := by
  simp [normalizedFlowDifferential, normalizedMaxCurve_initial]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.projectiveOriginalFlow_initial {y : ProjectiveState} (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) :
    projectiveOriginalFlow y t₀ t₀ = y := by
  rw [projectiveOriginalFlow, normalizedMaxCurve_initial]
  exact toProjectiveState_fromProjectiveState (ne_of_gt hD)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.projectiveFlowDifferential_initial {y : ProjectiveState} (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) :
    projectiveFlowDifferential y t₀ t₀ = ContinuousLinearMap.id ℝ ProjectiveState := by
  rw [projectiveFlowDifferential, normalizedMaxCurve_initial, normalizedFlowDifferential_initial,
    ContinuousLinearMap.id_comp, projective_chart_differential_inverse hD]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreProjectedFlowVariation_initial {y : ProjectiveState}
    (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) (w : ProjectiveState) :
    coreProjectedFlowVariation y t₀ t₀ w = coreClockProjection y w := by
  rw [coreProjectedFlowVariation, projectiveOriginalFlow_initial hD,
    projectiveFlowDifferential_initial hD, ContinuousLinearMap.id_apply]

end
end

/-- Every admissible large-core entrance has a first return and a uniform projected derivative bound. -/
theorem solution {k u w : ℝ} (hk : 6 ≤ k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    let y : ProjectiveState := ![1 + Real.sqrt (k ^ 2 - 1), u, 1, w]
    ∃ T > 0,
      IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} T ∧
      (∀ t ∈ Icc 0 T, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0 ∧
        coreRegion k (projectiveOriginalFlow y 0 t)) ∧
      ∀ t ∈ Icc 0 T, ∀ v : ProjectiveState,
        ‖scaleCoreVariation k (coreProjectedFlowVariation y 0 t v)‖ ≤
          ‖scaleCoreVariation k (coreClockProjection y v)‖ * coreVariationBound := by
  intro y
  have hD : 0 < projectiveStateDenom y :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (coreBootstrap_denom_lower hk hu hw)
  have hc : stateConstraint (fromProjectiveState y) = 1 := fromProjectiveState_constraint (ne_of_gt hD)
  obtain ⟨T, hT, hfirst, hcore, _⟩ := exists_large_core_traversal hk hu hw
  refine ⟨T, hT, hfirst, hcore, ?_⟩
  intro t ht v
  have hsub : Icc 0 t ⊆ Icc 0 T := fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
  have H := coreProjectedFlowVariation_growth hk ht.1 hD
    (fun s hs => normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs.1)
    (fun s hs => (hcore s (hsub hs)).1) (fun s hs => (hcore s (hsub hs)).2) v
  rw [coreProjectedFlowVariation_initial hD] at H
  exact H
