-- Prove2me | solution 1 for BianchiIX.coreRegion_log_rate_variation_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:35:29.061434+00:00
-- url     : https://prove2.me/submissions/00fb6b36-19b5-47a7-b0de-0abc07545842

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreAuxiliary
import Definitions.Def_BianchiIX_Dynamics_CoreWeightedVariation
import Definitions.Def_BianchiIX_Dynamics_CoreLogRates
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreBootstrap_original_clock_lower
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_coreLogRates_fderiv
import Theorems.Thm_BianchiIX_coreRegion_log_rate_bounds
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
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
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

private theorem BianchiIX.coreRadius_pos {m v : ℝ} (hv : 0 < v) : 0 < coreRadius m v := by
  apply Real.sqrt_pos.mpr
  unfold coreEnergy
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngle_sqrt {m v : ℝ} (hv : 0 < v) :
    Real.sqrt (1 + ((1 - m) / v) ^ 2) = coreRadius m v / v := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (div_nonneg (coreRadius_pos hv).le hv.le)).mpr
  simp only [div_pow, coreRadius_sq]
  unfold coreEnergy
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.cosh_coreAngle {m v : ℝ} (hv : 0 < v) :
    Real.cosh (coreAngle m v) = coreRadius m v / v := by
  rw [coreAngle, Real.cosh_arsinh, coreAngle_sqrt hv]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.tanh_coreAngle {m v : ℝ} (hv : 0 < v) :
    Real.tanh (coreAngle m v) = (1 - m) / coreRadius m v := by
  rw [coreAngle, Real.tanh_arsinh, coreAngle_sqrt hv]
  field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngle_coordinates {m v : ℝ} (hv : 0 < v) :
    coreRadius m v / Real.cosh (coreAngle m v) = v ∧
      1 - coreRadius m v * Real.tanh (coreAngle m v) = m := by
  have hr := ne_of_gt (coreRadius_pos (m := m) hv)
  rw [cosh_coreAngle hv, tanh_coreAngle hv]
  constructor
  · field_simp
  · field_simp
    ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreAuxiliary_projective_clockFactor {y : ProjectiveState} (hv : 0 < y 2) :
    coreAuxiliary (projectiveCoreAngle y) (toCoreAngleState y) 1 =
      coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3) := by
  change coreClockFactor (coreRadius (y 0) (y 2)) (y 1)
    (y 2 * y 3 / (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2)))) = _
  rw [(coreAngle_coordinates hv).1, mul_div_cancel_left₀ _ (ne_of_gt hv)]

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

private theorem BianchiIX.abs_three_row_le {a b c x y z A B C : ℝ}
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) :
    |a * x + b * y + c * z| ≤ A * |x| + B * |y| + C * |z| := by
  have H := (abs_add_le (a * x + b * y) (c * z)).trans
    (add_le_add (abs_add_le (a * x) (b * y)) (le_refl _))
  simp only [abs_mul] at H
  exact H.trans (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_right ha (abs_nonneg _))
    (mul_le_mul_of_nonneg_right hb (abs_nonneg _)))
    (mul_le_mul_of_nonneg_right hc (abs_nonneg _)))

/-- The weak rate retains the strongly damped variation instead of replacing it by its supremum. -/
theorem solution {k Q : ℝ} {y : ProjectiveState} {ξ : CoreAngleState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hQ : ‖scaleCoreVariation k ξ‖ ≤ Q) :
    let D := fderiv ℝ (coreLogRates (projectiveCoreAngle y)) (toCoreAngleState y) ξ
    |D 0| ≤ 3 * Q ∧ |D 1| ≤ (9 / k ^ 2) * Q + (8 / k) * |k * ξ 1| := by
  intro D
  let J := coreLogRateJacobian (projectiveCoreAngle y) (toCoreAngleState y)
  have hk0 : 0 < k := by linarith only [hk]
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans hQ
  have hc (i : Fin 3) : |scaleCoreVariation k ξ i| ≤ Q :=
    (show |scaleCoreVariation k ξ i| ≤ ‖scaleCoreVariation k ξ‖ from
      norm_le_pi_norm (scaleCoreVariation k ξ) i).trans hQ
  have hr : |ξ 0| ≤ Q := hc 0
  have hp : |ξ 2| ≤ Q := hc 2
  have hx : k * |ξ 1| ≤ Q := by simpa only [scaleCoreVariation, Matrix.cons_val_one,
    Matrix.cons_val_zero, abs_mul, abs_of_pos hk0] using hc 1
  have hu : |ξ 1| ≤ Q := by nlinarith only [hx, hk, abs_nonneg (ξ 1)]
  have hv : 0 < y 2 := lt_of_lt_of_le zero_lt_one hy.2.1
  have hd : coreAuxiliary (projectiveCoreAngle y) (toCoreAngleState y) 1 ≠ 0 := by
    rw [coreAuxiliary_projective_clockFactor hv]
    exact ne_of_gt (coreRegion_clock_regular hk hy).2.1
  have hD : D = J.mulVec ξ := coreLogRates_fderiv _ (ne_of_gt (coreRadius_pos hv)) hd ξ
  have hrow (i : Fin 2) : D i = J i 0 * ξ 0 + J i 1 * ξ 1 + J i 2 * ξ 2 := by
    rw [hD]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_assoc]
  obtain ⟨_, _, h00, h01, h02, h10, h11, h12⟩ := coreRegion_log_rate_bounds hk hy
  have hsmall : 4 * (1 / 10000 : ℝ) / k ^ 2 ≤ 1 / 100 := by
    apply (div_le_iff₀ (sq_pos_of_pos hk0)).mpr
    nlinarith only [hk]
  have hpk : 4 / k ≤ 2 / 3 := (div_le_iff₀ hk0).mpr (by linarith only [hk])
  constructor
  · rw [hrow 0]
    have H := abs_three_row_le h00 h01 h02 (x := ξ 0) (y := ξ 1) (z := ξ 2)
    have H' := H.trans (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 2))
      (mul_le_mul hsmall hu (abs_nonneg _) (by norm_num)))
      (mul_le_mul hpk hp (abs_nonneg _) (by norm_num)))
    linarith only [H', hQ0]
  · rw [hrow 1]
    have H := abs_three_row_le h10 h11 h12 (x := ξ 0) (y := ξ 1) (z := ξ 2)
    have H' := H.trans (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 8 / k ^ 2)) (le_refl _))
      (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 8 * (1 / 10000 : ℝ) / k ^ 2)))
    apply H'.trans
    rw [abs_mul, abs_of_pos hk0]
    have hcoeff : 8 / k ^ 2 + 8 * (1 / 10000 : ℝ) / k ^ 2 ≤ 9 / k ^ 2 := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg k)
    have HH := mul_le_mul_of_nonneg_right hcoeff hQ0
    have heq : (8 / k) * (k * |ξ 1|) = 8 * |ξ 1| := by field_simp
    rw [heq]
    linarith only [HH]
