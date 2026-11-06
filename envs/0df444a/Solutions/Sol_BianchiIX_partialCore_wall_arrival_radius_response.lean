-- Prove2me | solution 1 for BianchiIX.partialCore_wall_arrival_radius_response
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:31:48.307191+00:00
-- url     : https://prove2.me/submissions/7964e589-c26e-4b3b-b61a-ad29d26bdf53

import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreWeightedVariation
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_CoreExitFactor
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_Dynamics_CoreExitEvents
import Theorems.Thm_BianchiIX_coreClockProjection_growth
import Theorems.Thm_BianchiIX_coreWallArrivalDifferential_correction
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveFlowDifferential_apply
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_partialCore_exit_factor_bound
import Theorems.Thm_BianchiIX_partialCore_field_bounds
import Theorems.Thm_BianchiIX_partialCore_projectedFlowVariation_radius_drift
import Theorems.Thm_BianchiIX_partial_core_radius_arrival_error
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

private theorem BianchiIX.coreBootstrap_wall_bound {k u : ℝ} (hk : 6 ≤ k) (hu : u ≤ (1 / 10000) / k) :
    u ≤ 1 / 60000 := by
  have hk0 : 0 < k := by linarith
  exact hu.trans ((div_le_iff₀ hk0).mpr (by linarith))

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

private theorem BianchiIX.scaleCoreVariationLinear_apply (k : ℝ) (v : CoreAngleState) :
    scaleCoreVariationLinear k v = scaleCoreVariation k v := by
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.partialCore_weighted_field_bound {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k) :
    ‖scaleCoreVariation k (coreAngleField (projectiveCoreAngle y) (toCoreAngleState y))‖ ≤
      4 * (k ^ 2 * y 1 + (y 2 * y 3) / k) := by
  let F := coreAngleField (projectiveCoreAngle y) (toCoreAngleState y)
  let p := y 2 * y 3
  have hk0 : 0 < k := by linarith only [hk]
  have hu : 0 ≤ y 1 := hy.2.2.1.1
  have hp : 0 ≤ p := hy.2.2.2.1
  have hp1 : p ≤ 1 := (coreBootstrap_wall_bound hk hy.2.2.2.2).trans (by norm_num)
  have hp2 : p ^ 2 / k ≤ p / k := div_le_div_of_nonneg_right (by nlinarith only [hp, hp1]) hk0.le
  have hku : k * y 1 ≤ k ^ 2 * y 1 := by
    have H : k ≤ k ^ 2 := by nlinarith only [hk]
    exact mul_le_mul_of_nonneg_right H hu
  obtain ⟨hR', hU, hP⟩ := partialCore_field_bounds hk hy hR
  change |F 0| ≤ 2 * (k * y 1 + p ^ 2 / k) at hR'
  change |F 1| ≤ 2 * k * y 1 at hU
  change |F 2| ≤ 4 * p / k at hP
  rw [show 4 * p / k = 4 * (p / k) by ring] at hP
  have hpdiv : 0 ≤ p / k := div_nonneg hp hk0.le
  have hkusq : 0 ≤ k ^ 2 * y 1 := mul_nonneg (sq_nonneg _) hu
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro i
  fin_cases i
  · change |F 0| ≤ _
    linarith only [hR', hp2, hku, hkusq, hpdiv]
  · change |k * F 1| ≤ _
    rw [abs_mul, abs_of_pos hk0]
    nlinarith only [mul_le_mul_of_nonneg_left hU hk0.le, hkusq, hpdiv]
  · change |F 2| ≤ _
    linarith only [hP, hkusq]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.partialCore_moving_start_bound {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (v : CoreAngleState) (dz : ℝ) :
    ‖scaleCoreVariation k
      (v - dz • coreAngleField (projectiveCoreAngle y) (toCoreAngleState y))‖ ≤
      4 * partialCoreVariationBudget k (y 1) (y 2 * y 3) v dz := by
  have hk0 : 0 < k := by linarith only [hk]
  let N := |v 0| + k * |v 1| + |v 2|
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hv : ‖scaleCoreVariation k v‖ ≤ N := by
    apply (pi_norm_le_iff_of_nonempty _).mpr
    intro i
    fin_cases i
    · change |v 0| ≤ N
      dsimp [N]
      linarith only [mul_nonneg hk0.le (abs_nonneg (v 1)), abs_nonneg (v 2)]
    · change |k * v 1| ≤ N
      rw [abs_mul, abs_of_pos hk0]
      dsimp [N]
      linarith only [abs_nonneg (v 0), abs_nonneg (v 2)]
    · change |v 2| ≤ N
      dsimp [N]
      linarith only [abs_nonneg (v 0), mul_nonneg hk0.le (abs_nonneg (v 1))]
  have hfield := partialCore_weighted_field_bound hk hy hR
  rw [← scaleCoreVariationLinear_apply, map_sub, map_smul]
  calc
    _ ≤ ‖scaleCoreVariationLinear k v‖ +
        ‖dz • scaleCoreVariationLinear k
          (coreAngleField (projectiveCoreAngle y) (toCoreAngleState y))‖ := norm_sub_le _ _
    _ = ‖scaleCoreVariation k v‖ + |dz| *
        ‖scaleCoreVariation k (coreAngleField (projectiveCoreAngle y) (toCoreAngleState y))‖ := by
      rw [norm_smul, Real.norm_eq_abs, scaleCoreVariationLinear_apply, scaleCoreVariationLinear_apply]
    _ ≤ N + |dz| * (4 * (k ^ 2 * y 1 + (y 2 * y 3) / k)) :=
      add_le_add hv (mul_le_mul_of_nonneg_left hfield (abs_nonneg _))
    _ ≤ _ := by unfold partialCoreVariationBudget; dsimp [N] at hN ⊢; nlinarith only [hN]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.partialCore_clockProjection_bound {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (w : ProjectiveState) :
    ‖scaleCoreVariation k (coreClockProjection y w)‖ ≤
      4 * partialCoreVariationBudget k (y 1) (y 2 * y 3)
        (fderiv ℝ toCoreAngleState y w) (fderiv ℝ projectiveCoreAngle y w) :=
  partialCore_moving_start_bound hk hy hR _ _

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.partialCore_moving_variation_growth {beta v : ℝ → ProjectiveState} {k a b : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b)
    (hbeta : ∀ t ∈ Icc a b, HasDerivAt beta (projectiveOriginalField (beta t)) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (fderiv ℝ projectiveOriginalField (beta t) (v t)) t)
    (hregion : ∀ t ∈ Icc a b, coreRegion k (beta t))
    (hR : coreRadius (beta a 0) (beta a 2) = k) :
    ‖scaleCoreVariation k (coreClockProjection (beta b) (v b))‖ ≤
      4 * coreVariationBound * partialCoreVariationBudget k (beta a 1) (beta a 2 * beta a 3)
        (fderiv ℝ toCoreAngleState (beta a) (v a))
        (fderiv ℝ projectiveCoreAngle (beta a) (v a)) := by
  have H := coreClockProjection_growth hk hab hbeta hv hregion
  have H0 := partialCore_clockProjection_bound hk (hregion a ⟨le_rfl, hab⟩) hR (v a)
  have hC : 0 ≤ coreVariationBound := (Real.exp_pos _).le
  exact H.trans ((mul_le_mul_of_nonneg_right H0 hC).trans_eq (by ring))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.partialCore_projectedFlowVariation_bound {y : ProjectiveState} {t₀ k a b : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b) (hD : 0 < projectiveStateDenom y)
    (hdomain : Icc a b ⊆ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : ∀ t ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hregion : ∀ t ∈ Icc a b, coreRegion k (projectiveOriginalFlow y t₀ t))
    (hR : coreRadius (projectiveOriginalFlow y t₀ a 0) (projectiveOriginalFlow y t₀ a 2) = k)
    (w : ProjectiveState) :
    let beta := projectiveOriginalFlow y t₀
    let v := projectiveFlowDifferential y t₀ a w
    ‖scaleCoreVariation k (coreProjectedFlowVariation y t₀ b w)‖ ≤
      4 * coreVariationBound * partialCoreVariationBudget k (beta a 1) (beta a 2 * beta a 3)
        (fderiv ℝ toCoreAngleState (beta a) v) (fderiv ℝ projectiveCoreAngle (beta a) v) := by
  exact partialCore_moving_variation_growth (beta := projectiveOriginalFlow y t₀)
    (v := fun t => projectiveFlowDifferential y t₀ t w) hk hab
    (fun t ht => hasDerivAt_projectiveOriginalFlow_time hD (hdomain ht) (hA t ht))
    (fun t ht => hasDerivAt_projectiveFlowDifferential_apply hD (hdomain ht) (hA t ht) w)
    hregion hR

end
end


/-- Formula (E.20) for the genuine moving-wall differential of an arbitrary core prefix. -/
theorem solution {y : ProjectiveState} {t₀ k a b : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b) (hD : 0 < projectiveStateDenom y)
    (hdom : Icc a b ⊆ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : ∀ t ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hcore : ∀ t ∈ Icc a b, coreRegion k (projectiveOriginalFlow y t₀ t))
    (hR : coreRadius (projectiveOriginalFlow y t₀ a 0) (projectiveOriginalFlow y t₀ a 2) = k)
    (hV : projectiveOriginalFlow y t₀ b 2 = 1) (hM : projectiveOriginalFlow y t₀ b 0 < 1)
    (w : ProjectiveState) :
    let β := projectiveOriginalFlow y t₀
    let v := fderiv ℝ toCoreAngleState (β a) (projectiveFlowDifferential y t₀ a w)
    let dz := fderiv ℝ projectiveCoreAngle (β a) (projectiveFlowDifferential y t₀ a w)
    let U := β a 1
    let P := β a 2 * β a 3
    |(fderiv ℝ toCoreAngleState (β b) (projectiveWallArrivalDifferential y t₀ b w)) 0 - v 0| ≤
      4096 * coreVariationBound *
        (|v 1| + (U + P) * (|v 0| + |v 2|) / k + (k * U + P ^ 2 / k) * |dz|) := by
  intro β v dz U P
  let ξ := fun t => coreProjectedFlowVariation y t₀ t w
  let F := coreAngleField (projectiveCoreAngle (β a)) (toCoreAngleState (β a))
  let Q := (4 * coreVariationBound) * partialCoreVariationBudget k U P v dz
  have hk0 : 0 < k := by linarith only [hk]
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hQ (t : ℝ) (ht : t ∈ Icc a b) : ‖scaleCoreVariation k (ξ t)‖ ≤ Q := by
    have hsub : Icc a t ⊆ Icc a b := fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
    exact partialCore_projectedFlowVariation_bound hk ht.1 hD (fun _ hs => hdom (hsub hs))
      (fun s hs => hA s (hsub hs)) (fun s hs => hcore s (hsub hs)) hR w
  have hdrift := partialCore_projectedFlowVariation_radius_drift hk hab hD hdom hA hcore w hQ
  have hinit : ξ a = v - dz • F := rfl
  obtain ⟨hF0, hF1, _⟩ := partialCore_field_bounds hk (hcore a ha) hR
  change |F 0| ≤ 2 * (k * U + P ^ 2 / k) at hF0
  change |F 1| ≤ 2 * k * U at hF1
  have hr : |ξ a 0 - v 0| ≤ 2 * (k * U + P ^ 2 / k) * |dz| := by
    rw [hinit]
    change |(v 0 - dz * F 0) - v 0| ≤ _
    rw [sub_sub_cancel_left, abs_neg, abs_mul]
    exact (mul_le_mul_of_nonneg_left hF0 (abs_nonneg dz)).trans_eq (mul_comm _ _)
  have hx : |k * ξ a 1| ≤ k * |v 1| + 2 * k ^ 2 * U * |dz| := by
    rw [hinit]
    change |k * (v 1 - dz * F 1)| ≤ _
    rw [abs_mul, abs_of_pos hk0]
    have H := (abs_sub (v 1) (dz * F 1)).trans (add_le_add (le_refl |v 1|)
      (by simpa only [abs_mul] using mul_le_mul_of_nonneg_left hF1 (abs_nonneg dz)))
    have HH := mul_le_mul_of_nonneg_left H hk0.le
    convert! HH using 1
    ring
  obtain ⟨hs, hs1, hse⟩ := partialCore_exit_factor_bound hk hab hD hdom hA hcore hV hM
  have hsmall : U + P ≤ 1 := by
    have HU := coreBootstrap_wall_bound hk (hcore a ha).2.2.1.2
    have HP := coreBootstrap_wall_bound hk (hcore a ha).2.2.2.2
    change U ≤ 1 / 60000 at HU
    change P ≤ 1 / 60000 at HP
    linarith only [HU, HP]
  have hK : 1 ≤ coreVariationBound := Real.one_le_exp_iff.mpr (by positivity)
  have H := partial_core_radius_arrival_error hk (hcore a ha).2.2.1.1
    (hcore a ha).2.2.2.1 hsmall hK hs.le hs1 hse hr hx hdrift
  rw [(coreWallArrivalDifferential_correction hk hD (hdom hb) (hA b hb) (hcore b hb) hV hM w).2]
  exact H
