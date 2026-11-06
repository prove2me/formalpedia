-- Prove2me | solution 1 for BianchiIX.partialCore_exit_factor_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:06:39.396617+00:00
-- url     : https://prove2.me/submissions/6b9b3859-6148-4393-97c0-bd2afd5bb9e1

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_CoreExitFactor
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreBootstrap_original_clock_lower
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_coreRegion_exit_factor_bounds
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_coreAngle_scaled
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_normalized_core_prefix_contraction
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
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
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Positivity

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_sq (m v : ℝ) : coreRadius m v ^ 2 = coreEnergy m v :=
  Real.sq_sqrt (by unfold coreEnergy; positivity)

end
end

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
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_projectiveOriginalFlow_time {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) :
    HasDerivAt (projectiveOriginalFlow y t₀)
      (projectiveOriginalField (projectiveOriginalFlow y t₀ t)) t := by
  have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ t) = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  exact hasDerivAt_projectiveOriginalFlow (hasDerivAt_normalizedMaxCurve ht) (ne_of_gt hA) hc

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRegion_radius_bounds {k : ℝ} {y : ProjectiveState} (hk : 6 ≤ k) (hy : coreRegion k y) :
    99 / 100 * k ≤ coreRadius (y 0) (y 2) ∧ coreRadius (y 0) (y 2) ≤ 101 / 100 * k :=
  coreBootstrap_radius_closed hk (Real.sqrt_nonneg _)
    (by rw [coreRadius_sq]; exact hy.1)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRegion_wall_bounds {k : ℝ} {y : ProjectiveState} (hy : coreRegion k y) :
    (0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k) ∧ (0 ≤ y 3 ∧ y 3 ≤ (1 / 10000) / k) := by
  have hv0 : 0 < y 2 := lt_of_lt_of_le zero_lt_one hy.2.1
  have hw0 : 0 ≤ y 3 := (mul_nonneg_iff_of_pos_left hv0).mp hy.2.2.2.1
  exact ⟨hy.2.2.1, hw0, (le_mul_of_one_le_left hw0 hy.2.1).trans hy.2.2.2.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreRegion_clock_regular {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) :
    0 < projectiveStateDenom y ∧
      0 < coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3) ∧
        0 < coreOriginalClockRate y := by
  have hk0 : 0 < k := by linarith only [hk]
  have hr := coreRegion_radius_bounds hk hy
  obtain ⟨hu, hw⟩ := coreRegion_wall_bounds hy
  have hD := coreBootstrap_denom_lower (m := y 0) (v := y 2) hk hu hw
  have hd := (coreBootstrap_clock_bounds hk hr.1 hu hw).1
  have hrate := coreBootstrap_original_clock_lower hk hr (zero_le_one.trans hy.2.1) hu hw
  exact ⟨lt_of_lt_of_le (by norm_num) hD, lt_of_lt_of_le (by norm_num) hd,
    lt_of_lt_of_le (one_div_pos.mpr hk0) hrate⟩

end
end

theorem solution {y : ProjectiveState} {t₀ k a b : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b) (hD : 0 < projectiveStateDenom y)
    (hdom : Icc a b ⊆ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : ∀ t ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hcore : ∀ t ∈ Icc a b, coreRegion k (projectiveOriginalFlow y t₀ t))
    (hV : projectiveOriginalFlow y t₀ b 2 = 1) (hM : projectiveOriginalFlow y t₀ b 0 < 1) :
    let β := projectiveOriginalFlow y t₀
    0 < coreExitRadialFactor (β b) ∧ coreExitRadialFactor (β b) ≤ 1 ∧
      |coreExitRadialFactor (β b) - 1| ≤ 8 * (β a 1 / k + (β a 2 * β a 3) ^ 2 / k ^ 2) := by
  intro β
  let θ := fun t => projectiveCoreAngle (β t)
  have hk0 : 0 < k := by linarith only [hk]
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hθ (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt θ (coreOriginalClockRate (β t)) t :=
    hasDerivAt_coreAngle_scaled (hasDerivAt_projectiveOriginalFlow_time hD (hdom ht) (hA t ht))
      (zero_lt_one.trans_le (hcore t ht).2.1)
  have hmono : MonotoneOn θ (Icc a b) := monotoneOn_of_deriv_nonneg (convex_Icc a b)
    (fun t ht => (hθ t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hθ t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => by
      rw [(hθ t (interior_subset ht)).deriv]
      exact (coreRegion_clock_regular hk (hcore t (interior_subset ht))).2.2.le)
  obtain ⟨hU, hP⟩ := normalized_core_prefix_contraction hk (convex_Icc a b) hdom
    (fromProjectiveState_constraint (ne_of_gt hD)) hA ha hb hab
    (fun t ht => (coreRegion_radius_bounds hk (hcore t ht)).1)
    (fun t ht => (hcore t ht).2.1)
    (fun t ht => (coreRegion_wall_bounds (hcore t ht)).1)
    (fun t ht => (coreRegion_wall_bounds (hcore t ht)).2)
  have hexp : Real.exp (-k * (θ b - θ a) / 4) ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk0.le) (sub_nonneg.mpr (hmono ha hb hab)))
      (by norm_num))
  have hUle : β b 1 ≤ β a 1 := hU.trans
    (mul_le_of_le_one_right (hcore a ha).2.2.1.1 hexp)
  change β b 2 * β b 3 ≤ β a 2 * β a 3 at hP
  change β b 2 = 1 at hV
  rw [hV, one_mul] at hP
  obtain ⟨hpos, hle, herr⟩ := coreRegion_exit_factor_bounds hk (hcore b hb) hV hM
  refine ⟨hpos, hle, herr.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (add_le_add (div_le_div_of_nonneg_right hUle hk0.le)
    (div_le_div_of_nonneg_right ((sq_le_sq₀ (coreRegion_wall_bounds (hcore b hb)).2.1
      (hcore a ha).2.2.2.1).mpr hP) (sq_nonneg k))) (by norm_num)
