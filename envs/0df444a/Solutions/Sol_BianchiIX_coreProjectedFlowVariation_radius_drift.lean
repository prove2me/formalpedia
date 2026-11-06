-- Prove2me | solution 1 for BianchiIX.coreProjectedFlowVariation_radius_drift
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:37:50.578121+00:00
-- url     : https://prove2.me/submissions/4257a587-ac1a-4cdc-9ca2-94c231873fc5

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
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Theorems.Thm_BianchiIX_abs_sub_le_integral_bound
import Theorems.Thm_BianchiIX_contDiff_projectiveStateDenom
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreBootstrap_original_clock_lower
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_coreProjectedFlowVariation_strong_integrals
import Theorems.Thm_BianchiIX_coreRegion_radius_variation_row
import Theorems.Thm_BianchiIX_coreWeightedJacobian_mulVec
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_coreAngle_scaled
import Theorems.Thm_BianchiIX_hasDerivAt_coreProjectedFlowVariation
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_projectiveOriginalFlow_core_weight_integrals
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

private theorem BianchiIX.core_radius_integral_constants {k U P Q X : ℝ}
    (hk : 6 ≤ k) (hU : 0 ≤ U) (hP : 0 ≤ P) (hPk : P ≤ k) (hQ : 0 ≤ Q) (hX : 0 ≤ X) :
    (16 * Q) * (4 * U / k) + (8 * Q / k ^ 2) * (2 * (101 / 99 : ℝ) ^ 2 * P ^ 2) +
        (8 * Q) * (2 * (101 / 99 : ℝ) ^ 2 * P / k) +
        2 * ((12 * X + 432 * U * Q) / k ^ 2) + (1 / k) * ((4 * X + 48 * U * Q) / k) ≤
      256 * (X / k ^ 2 + (U + P) * Q / k) := by
  have hk0 : 0 < k := by linarith only [hk]
  have hUk := mul_le_mul_of_nonneg_right hk (mul_nonneg hU hQ)
  have hP2 := mul_le_mul_of_nonneg_right hPk (mul_nonneg hP hQ)
  have hUQk := mul_nonneg (mul_nonneg hU hQ) hk0.le
  have hPQk := mul_nonneg (mul_nonneg hP hQ) hk0.le
  have hP2Q := mul_nonneg (sq_nonneg P) hQ
  apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hk0)).mp
  field_simp
  nlinarith only [hX, hUk, hP2, hUQk, hPQk, hP2Q]

/-- The radius component of the genuine fixed-angle variation has an integrable amplitude-sensitive drift. -/
theorem solution {y : ProjectiveState} {t₀ k a b Q : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b) (hD : 0 < projectiveStateDenom y)
    (hdom : Icc a b ⊆ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : ∀ t ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hcore : ∀ t ∈ Icc a b, coreRegion k (projectiveOriginalFlow y t₀ t))
    (hentry : Real.cosh (projectiveCoreAngle (projectiveOriginalFlow y t₀ a)) = k)
    (w : ProjectiveState)
    (hQ : ∀ t ∈ Icc a b, ‖scaleCoreVariation k (coreProjectedFlowVariation y t₀ t w)‖ ≤ Q) :
    let β := projectiveOriginalFlow y t₀
    let ξ := fun t => coreProjectedFlowVariation y t₀ t w
    |ξ b 0 - ξ a 0| ≤ 256 * (|k * ξ a 1| / k ^ 2 + (β a 1 + β a 2 * β a 3) * Q / k) := by
  intro β ξ
  let θ := fun t => projectiveCoreAngle (β t)
  let rate := fun t => coreOriginalClockRate (β t)
  let x := fun t => k * ξ t 1
  let u := fun t => β t 1 * rate t
  let w₂ := fun t => β t 3 ^ 2 * rate t
  let wv := fun t => (β t 3 / (k * β t 2)) * rate t
  let xs := fun t => (|x t| / Real.cosh (θ t)) * rate t
  let xa := fun t => |x t| * rate t
  let A := fun t => (16 * Q) * u t + (8 * Q / k ^ 2) * w₂ t + (8 * Q) * wv t + 2 * xs t + (1 / k) * xa t
  have hk0 : 0 < k := by linarith only [hk]
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
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
  have hc (i : Fin 4) : ContinuousOn (fun t => β t i) (Icc a b) :=
    fun t ht => (hasDerivAt_pi.mp (hflow t ht) i).continuousAt.continuousWithinAt
  have hξ (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt ξ
      (rate t • (coreAngleJacobian (θ t) (toCoreAngleState (β t))).mulVec (ξ t)) t :=
    hasDerivAt_coreProjectedFlowVariation hD (hdom ht) (hA t ht) (hV t ht)
      (ne_of_gt (coreRegion_clock_regular hk (hcore t ht)).2.1) w
  have hxc : ContinuousOn x (Icc a b) := fun t ht =>
    ((hasDerivAt_pi.mp (hξ t ht) 1).const_mul k).continuousAt.continuousWithinAt
  have hθc : ContinuousOn θ (Icc a b) := fun t ht => (hθ t ht).continuousAt.continuousWithinAt
  have hu : ContinuousOn u (Icc a b) := (hc 1).mul hrate
  have hw₂ : ContinuousOn w₂ (Icc a b) := ((hc 3).pow 2).mul hrate
  have hwv : ContinuousOn wv (Icc a b) :=
    ((hc 3).div (continuousOn_const.mul (hc 2)) (fun t ht => ne_of_gt (mul_pos hk0 (hV t ht)))).mul hrate
  have hxs : ContinuousOn xs (Icc a b) := (hxc.abs.div
    (Real.continuous_cosh.comp_continuousOn hθc) (fun t _ => ne_of_gt (Real.cosh_pos _))).mul hrate
  have hxa : ContinuousOn xa (Icc a b) := hxc.abs.mul hrate
  have hAc : ContinuousOn A (Icc a b) :=
    ((((hu.const_mul _).add (hw₂.const_mul _)).add (hwv.const_mul _)).add (hxs.const_mul _)).add (hxa.const_mul _)
  have hbound (t : ℝ) (ht : t ∈ Icc a b) :
      |rate t * (coreAngleJacobian (θ t) (toCoreAngleState (β t))).mulVec (ξ t) 0| ≤ A t := by
    have H := coreRegion_radius_variation_row hk (hcore t ht) (hQ t ht)
    dsimp only at H
    rw [coreWeightedJacobian_mulVec (ne_of_gt hk0)] at H
    have H' := mul_le_mul_of_nonneg_left H (hpos t ht)
    rw [abs_mul, abs_of_nonneg (hpos t ht)]
    convert! H' using 1
    dsimp [A, u, w₂, wv, xs, xa, x, scaleCoreVariation, θ]
    ring
  have hdiff := abs_sub_le_integral_bound hab
    (fun t ht => hasDerivAt_pi.mp (hξ t ht) 0) hAc hbound
  have hi₁ := (hu.const_mul (16 * Q)).intervalIntegrable_of_Icc (μ := volume) hab
  have hi₂ := (hw₂.const_mul (8 * Q / k ^ 2)).intervalIntegrable_of_Icc (μ := volume) hab
  have hi₃ := (hwv.const_mul (8 * Q)).intervalIntegrable_of_Icc (μ := volume) hab
  have hi₄ := (hxs.const_mul 2).intervalIntegrable_of_Icc (μ := volume) hab
  have hi₅ := (hxa.const_mul (1 / k)).intervalIntegrable_of_Icc (μ := volume) hab
  have hlin : (∫ t in a..b, A t) =
      (16 * Q) * (∫ t in a..b, u t) + (8 * Q / k ^ 2) * (∫ t in a..b, w₂ t) +
        (8 * Q) * (∫ t in a..b, wv t) + 2 * (∫ t in a..b, xs t) + (1 / k) * (∫ t in a..b, xa t) := by
    dsimp only [A]
    rw [intervalIntegral.integral_add (((hi₁.add hi₂).add hi₃).add hi₄) hi₅,
      intervalIntegral.integral_add ((hi₁.add hi₂).add hi₃) hi₄,
      intervalIntegral.integral_add (hi₁.add hi₂) hi₃, intervalIntegral.integral_add hi₁ hi₂]
    simp only [intervalIntegral.integral_const_mul]
  obtain ⟨hUint, _, hWVint, hW₂int⟩ := projectiveOriginalFlow_core_weight_integrals hk hab hD hdom hA hcore
  obtain ⟨hXSint, hXAint⟩ := coreProjectedFlowVariation_strong_integrals hk hab hD hdom hA hcore hentry w hQ
  have hint := add_le_add (add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hUint (by positivity : 0 ≤ 16 * Q))
    (mul_le_mul_of_nonneg_left hW₂int (by positivity : 0 ≤ 8 * Q / k ^ 2)))
    (mul_le_mul_of_nonneg_left hWVint (by positivity : 0 ≤ 8 * Q)))
    (mul_le_mul_of_nonneg_left hXSint (by norm_num : (0 : ℝ) ≤ 2)))
    (mul_le_mul_of_nonneg_left hXAint (by positivity : 0 ≤ 1 / k))
  have hPk : β a 2 * β a 3 ≤ k := by
    have H := coreBootstrap_wall_bound hk (hcore a ha).2.2.2.2
    linarith only [H, hk]
  exact hdiff.trans (hlin.le.trans (hint.trans (core_radius_integral_constants hk
    (hcore a ha).2.2.1.1 (hcore a ha).2.2.2.1 hPk hQ0 (abs_nonneg _))))
