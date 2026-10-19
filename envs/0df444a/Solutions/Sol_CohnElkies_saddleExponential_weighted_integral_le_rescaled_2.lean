-- Prove2me | solution 2 for CohnElkies.saddleExponential_weighted_integral_le_rescaled
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:13:22.283397+00:00
-- url     : https://prove2.me/submissions/00aeced2-3f81-46b2-b45a-fea86805107c

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
theorem h47_int_abs_pow_exp (n : ℕ) {a : ℝ} (ha : 0 < a) :
    MeasureTheory.Integrable (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) := by
  have h1 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := a)
    (by have := n.cast_nonneg (α := ℝ); linarith) one_pos ha
  have hIoi : MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) (Set.Ioi 0) := by
    refine h1.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx0 : (0:ℝ) < x := hx
    simp [abs_of_pos hx0, Real.rpow_natCast]
  have hIio : MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) (Set.Iio 0) := by
    have := (show MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) (Set.Ioi (-0)) by
      simpa using hIoi).comp_neg_Iio
    simpa [abs_neg] using this
  have hall : MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) (Set.Iic 0 ∪ Set.Ioi 0) :=
    ((integrableOn_Iic_iff_integrableOn_Iio (b := (0:ℝ))).mpr hIio).union hIoi
  rw [Set.Iic_union_Ioi, MeasureTheory.integrableOn_univ] at hall
  exact hall

theorem solution
    {k : ℝ} (hk : 0 < k) :
    (∫ T : ℝ,
      saddleGaussianTailWeight T *
        Real.exp (-k * |T|)) ≤
      2 * max (1 : ℝ) (((k / 6) ^ 3)⁻¹) *
        (2 / (k / 2)) := by
  have hk2 : 0 < k / 2 := by positivity
  set M := max 1 ((k / 6) ^ 3)⁻¹ with hMdef
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM2 : ((k / 6) ^ 3)⁻¹ ≤ M := le_max_right _ _
  have hpt : ∀ T : ℝ, saddleGaussianTailWeight T * Real.exp (-k * |T|) ≤
      2 * M * Real.exp (-(k / 2) * |T|) := by
    intro T
    unfold saddleGaussianTailWeight
    have ht := abs_nonneg T
    have hy : 0 ≤ k * |T| / 6 := by positivity
    have hey : k * |T| / 6 ≤ Real.exp (k * |T| / 6) := by
      linarith [Real.add_one_le_exp (k * |T| / 6)]
    have hcube : (k * |T| / 6) ^ 3 ≤ Real.exp (k * |T| / 2) := by
      have : Real.exp (k * |T| / 2) = (Real.exp (k * |T| / 6)) ^ 3 := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      rw [this]; exact pow_le_pow_left₀ hy hey 3
    have hT3 : |T| ^ 3 = ((k / 6) ^ 3)⁻¹ * (k * |T| / 6) ^ 3 := by
      field_simp
    have hE1 : 1 ≤ Real.exp (k * |T| / 2) := Real.one_le_exp (by positivity)
    have hA : 1 + |T| ^ 3 ≤ 2 * M * Real.exp (k * |T| / 2) := by
      have h3 : |T| ^ 3 ≤ M * Real.exp (k * |T| / 2) := by
        rw [hT3]; exact mul_le_mul hM2 hcube (by positivity) (by linarith)
      have h1 : 1 ≤ M * Real.exp (k * |T| / 2) := by nlinarith
      linarith
    have hexp : Real.exp (k * |T| / 2) * Real.exp (-k * |T|) = Real.exp (-(k / 2) * |T|) := by
      rw [← Real.exp_add]; congr 1; ring
    calc (1 + |T| ^ 3) * Real.exp (-k * |T|)
        ≤ 2 * M * Real.exp (k * |T| / 2) * Real.exp (-k * |T|) :=
          mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
      _ = 2 * M * Real.exp (-(k / 2) * |T|) := by rw [mul_assoc, hexp]
  have hint1 : Integrable (fun T : ℝ => saddleGaussianTailWeight T * Real.exp (-k * |T|)) := by
    refine ((h47_int_abs_pow_exp 0 hk).add (h47_int_abs_pow_exp 3 hk)).congr
      (Filter.Eventually.of_forall fun T => ?_)
    simp only [Pi.add_apply, saddleGaussianTailWeight, pow_zero, one_mul]
    ring
  have hint2 : Integrable (fun T : ℝ => 2 * M * Real.exp (-(k / 2) * |T|)) := by
    refine ((h47_int_abs_pow_exp 0 hk2).const_mul (2 * M)).congr
      (Filter.Eventually.of_forall fun T => ?_)
    simp
  calc (∫ T : ℝ, saddleGaussianTailWeight T * Real.exp (-k * |T|))
      ≤ ∫ T : ℝ, 2 * M * Real.exp (-(k / 2) * |T|) := integral_mono hint1 hint2 hpt
    _ = 2 * M * (2 / (k / 2)) := by
      rw [MeasureTheory.integral_const_mul, integral_comp_abs (f := fun T => Real.exp (-(k / 2) * T)),
        integral_exp_mul_Ioi (by linarith : -(k / 2) < 0) 0]
      simp only [mul_zero, Real.exp_zero]
      field_simp

