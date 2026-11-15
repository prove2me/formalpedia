-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a255_HJB_weighted_factor_positive_origin_uniform_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:17:11.836235+00:00
-- url     : https://prove2.me/submissions/8f58b4ee-7a37-4f31-85a2-dc32858dc3ce

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a251_positive_interval_lower_derivative_bounds_value_above_near_origin
import Theorems.Thm_AvramDividend_Classical_avram_ga_a252_Gauss_HJB_derivative_of_positive_exponential_weighted_value
import Theorems.Thm_AvramDividend_Classical_avram_ga_a253_Gauss_HJB_weighted_first_derivative_factor_product_identity
import Theorems.Thm_AvramDividend_Classical_avram_ga_a254_Gauss_HJB_attenuated_above_lower_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (f fp : ℝ → ℝ) (a alpha beta : ℝ)
    (ha : 0 < a) (hAlpha : 0 ≤ alpha) (hBeta : beta ≤ alpha)
    (hCont : ContinuousOn f (Set.Ioi 0))
    (hf : ∀ t ∈ Set.Ioo 0 a, HasDerivAt f (fp t) t)
    (hFactor : ∀ t ∈ Set.Ioo 0 a,
      Real.exp (-beta*a)*(fp a-alpha*f a) ≤
      Real.exp (-beta*t)*(fp t-alpha*f t)) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y : ℝ, 0 < y → y ≤ a → f y ≤ K := by
  let h : ℝ → ℝ := fun t => Real.exp (-alpha*t)*f t
  let g0 : ℝ := Real.exp (-beta*a)*(fp a-alpha*f a)
  let B : ℝ := |h a|+|g0| * a
  let K : ℝ := Real.exp (alpha*a)*B
  have hB : 0 ≤ B := by
    dsimp [B]
    have hpos1 : 0 ≤ |h a| := abs_nonneg _
    have hpos2 : 0 ≤ |g0| := abs_nonneg _
    have hprod : 0 ≤ |g0| * a := mul_nonneg hpos2 ha.le
    linarith
  have hK : 0 ≤ K := mul_nonneg (Real.exp_nonneg _) hB
  refine ⟨K,hK,?_⟩
  intro y hy hya
  have hSub : Set.Icc y a ⊆ Set.Ioi (0:ℝ) := by
    intro t ht
    exact lt_of_lt_of_le hy ht.1
  have hc : ContinuousOn h (Set.Icc y a) := by
    exact (Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).continuousOn.mul
        (hCont.mono hSub)
  have hd : DifferentiableOn ℝ h (interior (Set.Icc y a)) := by
    intro t ht
    have hti : t ∈ Set.Ioo y a := by simpa [interior_Icc] using ht
    have ht0 : t ∈ Set.Ioo (0:ℝ) a := ⟨lt_trans hy hti.1,hti.2⟩
    exact (avram_ga_a252_Gauss_HJB_derivative_of_positive_exponential_weighted_value
      f fp alpha t (hf t ht0)).differentiableAt.differentiableWithinAt
  have hDeriv (t : ℝ) (ht : t ∈ interior (Set.Icc y a)) :
      -|g0| ≤ deriv h t := by
    have hti : t ∈ Set.Ioo y a := by simpa [interior_Icc] using ht
    have ht0 : t ∈ Set.Ioo (0:ℝ) a := ⟨lt_trans hy hti.1,hti.2⟩
    have hEq := (avram_ga_a252_Gauss_HJB_derivative_of_positive_exponential_weighted_value
      f fp alpha t (hf t ht0)).deriv
    have hRew := avram_ga_a253_Gauss_HJB_weighted_first_derivative_factor_product_identity
      (f t) (fp t) alpha beta t
    have hExp : Real.exp ((beta-alpha)*t) ≤ 1 :=
      Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hBeta) ht0.1.le)
    have hBound := avram_ga_a254_Gauss_HJB_attenuated_above_lower_bound
      g0 (Real.exp (-beta*t)*(fp t-alpha*f t))
      (Real.exp ((beta-alpha)*t)) (Real.exp_nonneg _) hExp
      (hFactor t ht0)
    rw [hEq,hRew]
    exact hBound
  have hY := avram_ga_a251_positive_interval_lower_derivative_bounds_value_above_near_origin
    h a y |g0| hya hc hd hDeriv
  have hYC : h y ≤ B := by
    dsimp [B]
    have hA := le_abs_self (h a)
    have hAbs := abs_nonneg g0
    nlinarith
  have hExp : Real.exp (alpha*y) ≤ Real.exp (alpha*a) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hya hAlpha)
  have hCancel : Real.exp (alpha*y)*Real.exp (-alpha*y) = 1 := by
    rw [←Real.exp_add]
    simp
  calc
    f y = Real.exp (alpha*y)*h y := by
      dsimp [h]
      rw [←mul_assoc,hCancel,one_mul]
    _ ≤ Real.exp (alpha*y)*B :=
      mul_le_mul_of_nonneg_left hYC (Real.exp_nonneg _)
    _ ≤ Real.exp (alpha*a)*B :=
      mul_le_mul_of_nonneg_right hExp hB
    _ = K := rfl
