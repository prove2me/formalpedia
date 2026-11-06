-- Prove2me | solution 1 for BianchiIX.partialCore_log_integral_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:29:55.242201+00:00
-- url     : https://prove2.me/submissions/848aea72-97e8-4aa0-9989-6c06a2737397

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreLinearization
import Definitions.Def_BianchiIX_Dynamics_CoreWeightedVariation
import Definitions.Def_BianchiIX_Dynamics_CoreLogRates
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Theorems.Thm_BianchiIX_contDiff_projectiveStateDenom
import Theorems.Thm_BianchiIX_coreBootstrap_angle_bound
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreBootstrap_original_clock_lower
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_coreProjectedFlowVariation_strong_bound
import Theorems.Thm_BianchiIX_coreRegion_log_rate_variation_bound
import Theorems.Thm_BianchiIX_core_clock_forced_variation_integrals
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_coreAngle_scaled
import Theorems.Thm_BianchiIX_hasDerivAt_coreProjectedFlowVariation
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Module
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
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
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section
open BianchiIX
open Set MeasureTheory

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

private theorem BianchiIX.coreRadius_pos {m v : ℝ} (hv : 0 < v) : 0 < coreRadius m v := by
  apply Real.sqrt_pos.mpr
  unfold coreEnergy
  positivity

end
end

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

private theorem BianchiIX.contDiffAt_projectiveCoreRadius (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) : ContDiffAt ℝ n (fun z : ProjectiveState => coreRadius (z 0) (z 2)) y := by
  have he : coreEnergy (y 0) (y 2) ≠ 0 := by unfold coreEnergy; positivity
  have he' : (y 0 - 1) ^ 2 + y 2 ^ 2 ≠ 0 := he
  unfold coreRadius coreEnergy
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_coreOriginalClockRate (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) (hD : projectiveStateDenom y ≠ 0) :
    ContDiffAt ℝ n coreOriginalClockRate y := by
  have hr := contDiffAt_projectiveCoreRadius n hv
  have hr2 : coreRadius (y 0) (y 2) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (coreRadius_pos hv))
  have hden := (contDiff_projectiveStateDenom n).contDiffAt (x := y)
  unfold coreOriginalClockRate coreClockFactor
  fun_prop

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
open Set MeasureTheory

private theorem BianchiIX.partial_core_clock_variation_integral {x z rate : ℝ → ℝ} {k a b U Q : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b) (hU : 0 ≤ U) (hQ : 0 ≤ Q)
    (hx : ContinuousOn x (Icc a b)) (hz : ∀ t ∈ Icc a b, HasDerivAt z (rate t) t)
    (hrate : ContinuousOn rate (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 ≤ rate t)
    (hbound : ∀ t ∈ Icc a b, |x t| ≤ Real.exp (-k * (z t - z a) / 4) *
      (|x a| + 3 * k * U * Q * (z t - z a))) :
    (∫ t in a..b, |x t| * rate t) ≤ (4 * |x a| + 48 * U * Q) / k := by
  let Z := fun t => z t - z a + Real.arcosh k
  have hZ (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt Z (rate t) t :=
    ((hz t ht).sub_const (z a)).add_const (Real.arcosh k)
  have hentry : Real.cosh (Z a) = k := by
    simp only [Z, sub_self, zero_add]
    exact Real.cosh_arcosh (by linarith only [hk])
  have hdiff (t : ℝ) : Z t - Z a = z t - z a := by dsimp [Z]; ring
  exact (core_clock_forced_variation_integrals hk hab hU hQ hx hZ hrate hpos hentry
    (fun t ht => by rw [hdiff]; exact hbound t ht)).2

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

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.partialCore_projectedFlowVariation_strong_integral {y : ProjectiveState} {t₀ k a b Q : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b) (hD : 0 < projectiveStateDenom y)
    (hdom : Icc a b ⊆ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : ∀ t ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hcore : ∀ t ∈ Icc a b, coreRegion k (projectiveOriginalFlow y t₀ t))
    (w : ProjectiveState)
    (hQ : ∀ t ∈ Icc a b, ‖scaleCoreVariation k (coreProjectedFlowVariation y t₀ t w)‖ ≤ Q) :
    let rate := fun t => coreOriginalClockRate (projectiveOriginalFlow y t₀ t)
    let x := fun t => k * coreProjectedFlowVariation y t₀ t w 1
    (∫ t in a..b, |x t| * rate t) ≤
      (4 * |x a| + 48 * projectiveOriginalFlow y t₀ a 1 * Q) / k := by
  intro rate x
  let θ := fun t => projectiveCoreAngle (projectiveOriginalFlow y t₀ t)
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hQ a ⟨le_rfl, hab⟩)
  have hV (t : ℝ) (ht : t ∈ Icc a b) : 0 < projectiveOriginalFlow y t₀ t 2 :=
    lt_of_lt_of_le zero_lt_one (hcore t ht).2.1
  have hflow (t : ℝ) (ht : t ∈ Icc a b) := hasDerivAt_projectiveOriginalFlow_time hD (hdom ht) (hA t ht)
  have hθ (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt θ (rate t) t :=
    hasDerivAt_coreAngle_scaled (hflow t ht) (hV t ht)
  have hrate : ContinuousOn rate (Icc a b) := by
    intro t ht
    exact ((contDiffAt_coreOriginalClockRate 1 (hV t ht)
      (ne_of_gt (coreRegion_clock_regular hk (hcore t ht)).1)).continuousAt.comp
        (hflow t ht).continuousAt).continuousWithinAt
  have hx : ContinuousOn x (Icc a b) := by
    intro t ht
    have H := hasDerivAt_coreProjectedFlowVariation hD (hdom ht) (hA t ht) (hV t ht)
      (ne_of_gt (coreRegion_clock_regular hk (hcore t ht)).2.1) w
    exact ((hasDerivAt_pi.mp H 1).const_mul k).continuousAt.continuousWithinAt
  exact partial_core_clock_variation_integral hk hab (hcore a ⟨le_rfl, hab⟩).2.2.1.1 hQ0 hx hθ hrate
    (fun t ht => (coreRegion_clock_regular hk (hcore t ht)).2.2.le)
    (coreProjectedFlowVariation_strong_bound hk hab hD hdom hA hcore w hQ)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.core_log_lower_bound {k : ℝ} (hk : 6 ≤ k) : 1 ≤ Real.log (4 * k) := by
  have H := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
  norm_num at H
  exact H.trans (Real.log_le_log (by norm_num) (by linarith only [hk]))

end
end


/-- The strongly damped component supplies the extra inverse-radius power for the weak multiplier. -/
theorem solution {y : ProjectiveState} {t₀ k a b Q : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b) (hD : 0 < projectiveStateDenom y)
    (hdom : Icc a b ⊆ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : ∀ t ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hcore : ∀ t ∈ Icc a b, coreRegion k (projectiveOriginalFlow y t₀ t))
    (w : ProjectiveState)
    (hQ : ∀ t ∈ Icc a b, ‖scaleCoreVariation k (coreProjectedFlowVariation y t₀ t w)‖ ≤ Q) :
    let β := projectiveOriginalFlow y t₀
    let I := fun i : Fin 2 => ∫ t in a..b, coreOriginalClockRate (β t) *
      (fderiv ℝ (coreLogRates (projectiveCoreAngle (β t))) (toCoreAngleState (β t))
        (coreProjectedFlowVariation y t₀ t w)) i
    |I 0| ≤ 6 * Real.log (4 * k) * Q ∧
      |I 1| ≤ 51 * Real.log (4 * k) * Q / k ^ 2 := by
  intro β I
  let θ := fun t => projectiveCoreAngle (β t)
  let rate := fun t => coreOriginalClockRate (β t)
  let x := fun t => k * coreProjectedFlowVariation y t₀ t w 1
  have hk0 : 0 < k := by linarith only [hk]
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hQ a ha)
  have hV (t : ℝ) (ht : t ∈ Icc a b) : 0 < β t 2 :=
    lt_of_lt_of_le zero_lt_one (hcore t ht).2.1
  have hflow (t : ℝ) (ht : t ∈ Icc a b) := hasDerivAt_projectiveOriginalFlow_time hD (hdom ht) (hA t ht)
  have hθ (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt θ (rate t) t :=
    hasDerivAt_coreAngle_scaled (hflow t ht) (hV t ht)
  have hrate : ContinuousOn rate (Icc a b) := by
    intro t ht
    exact ((contDiffAt_coreOriginalClockRate 1 (hV t ht)
      (ne_of_gt (coreRegion_clock_regular hk (hcore t ht)).1)).continuousAt.comp
        (hflow t ht).continuousAt).continuousWithinAt
  have hpos (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ rate t :=
    (coreRegion_clock_regular hk (hcore t ht)).2.2.le
  have hx : ContinuousOn x (Icc a b) := by
    intro t ht
    have H := hasDerivAt_coreProjectedFlowVariation hD (hdom ht) (hA t ht) (hV t ht)
      (ne_of_gt (coreRegion_clock_regular hk (hcore t ht)).2.1) w
    exact ((hasDerivAt_pi.mp H 1).const_mul k).continuousAt.continuousWithinAt
  have hspan : (∫ t in a..b, rate t) ≤ 2 * Real.log (4 * k) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hθ t (uIcc_of_le hab ▸ ht)) (hrate.intervalIntegrable_of_Icc hab)]
    have hangle (t : ℝ) (ht : t ∈ Icc a b) : |θ t| ≤ Real.log (4 * k) :=
      coreBootstrap_angle_bound hk (coreRegion_radius_bounds hk (hcore t ht)).2 (hcore t ht).2.1
    linarith only [(abs_le.mp (hangle a ha)).1, (abs_le.mp (hangle b hb)).2]
  have hbound (t : ℝ) (ht : t ∈ Icc a b) := coreRegion_log_rate_variation_bound hk (hcore t ht) (hQ t ht)
  constructor
  · have H := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hab
      (f := fun t => rate t * (fderiv ℝ (coreLogRates (θ t)) (toCoreAngleState (β t))
        (coreProjectedFlowVariation y t₀ t w)) 0)
      (g := fun t => (3 * Q) * rate t) (Filter.Eventually.of_forall (fun t ht => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hpos t (Ioc_subset_Icc_self ht))]
        exact (mul_le_mul_of_nonneg_left (hbound t (Ioc_subset_Icc_self ht)).1
          (hpos t (Ioc_subset_Icc_self ht))).trans_eq (by ring)))
      ((continuousOn_const.mul hrate).intervalIntegrable_of_Icc hab)
    rw [intervalIntegral.integral_const_mul] at H
    exact H.trans ((mul_le_mul_of_nonneg_left hspan (by positivity)).trans_eq (by ring))
  · have h1 : IntervalIntegrable (fun t => (9 / k ^ 2 * Q) * rate t) volume a b :=
      (continuousOn_const.mul hrate).intervalIntegrable_of_Icc hab
    have h2 : IntervalIntegrable (fun t => (8 / k) * (|x t| * rate t)) volume a b :=
      (continuousOn_const.mul (hx.abs.mul hrate)).intervalIntegrable_of_Icc hab
    have H := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hab
      (f := fun t => rate t * (fderiv ℝ (coreLogRates (θ t)) (toCoreAngleState (β t))
        (coreProjectedFlowVariation y t₀ t w)) 1)
      (g := fun t => (9 / k ^ 2 * Q) * rate t + (8 / k) * (|x t| * rate t))
      (Filter.Eventually.of_forall (fun t ht => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hpos t (Ioc_subset_Icc_self ht))]
        exact (mul_le_mul_of_nonneg_left (hbound t (Ioc_subset_Icc_self ht)).2
          (hpos t (Ioc_subset_Icc_self ht))).trans_eq (by dsimp [x]; ring))) (h1.add h2)
    rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at H
    have hstrong := partialCore_projectedFlowVariation_strong_integral hk hab hD hdom hA hcore w hQ
    have hX : |x a| ≤ Q := (norm_le_pi_norm
      (scaleCoreVariation k (coreProjectedFlowVariation y t₀ a w)) 1).trans (hQ a ha)
    have hU : β a 1 ≤ 1 / 60000 := coreBootstrap_wall_bound hk (hcore a ha).2.2.1.2
    have hsmall : 32 * |x a| + 384 * β a 1 * Q ≤ 33 * Q := by
      nlinarith only [hX, mul_le_mul_of_nonneg_right hU hQ0, hQ0]
    have HI : (8 / k) * (∫ t in a..b, |x t| * rate t) ≤ 33 * Q / k ^ 2 := by
      calc
        _ ≤ (8 / k) * ((4 * |x a| + 48 * β a 1 * Q) / k) :=
          mul_le_mul_of_nonneg_left hstrong (by positivity)
        _ = (32 * |x a| + 384 * β a 1 * Q) / k ^ 2 := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hsmall (sq_nonneg k)
    apply H.trans
    calc
      _ ≤ (9 / k ^ 2 * Q) * (2 * Real.log (4 * k)) + 33 * Q / k ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hspan (by positivity)) HI
      _ ≤ 51 * Real.log (4 * k) * Q / k ^ 2 := by
        have hlog := mul_le_mul_of_nonneg_right (core_log_lower_bound hk) hQ0
        apply (div_le_div_of_nonneg_right (show
          18 * Real.log (4 * k) * Q + 33 * Q ≤ 51 * Real.log (4 * k) * Q by
            nlinarith only [hlog]) (sq_nonneg k)).trans_eq' ?_
        ring
