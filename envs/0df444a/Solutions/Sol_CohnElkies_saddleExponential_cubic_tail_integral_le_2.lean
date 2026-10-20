-- Prove2me | solution 2 for CohnElkies.saddleExponential_cubic_tail_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:14:47.95398+00:00
-- url     : https://prove2.me/submissions/d5db2f43-004f-4d40-9406-f7c6f28f57a5

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
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
    {k R : ℝ} (hk : 6 ≤ k) (hR : 0 ≤ R) :
    (∫ T : ℝ in saddleGaussianTailSet R,
      saddleGaussianTailWeight T *
        Real.exp (-k * |T|)) ≤
      2 * Real.exp (-(k / 4) * R) *
        (2 / (k / 4)) := by
  set c : ℝ := k / 4 with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  have hkpos : 0 < k := by linarith
  set g : ℝ → ℝ := fun T => 2 * Real.exp (-c * |T|) with hg
  have hgint : Integrable g := by
    have := (h47_int_abs_pow_exp 0 hcpos).const_mul 2
    simpa [hg] using this
  have hfint : Integrable (fun T : ℝ => saddleGaussianTailWeight T * Real.exp (-k * |T|)) := by
    unfold saddleGaussianTailWeight
    have := (h47_int_abs_pow_exp 0 hkpos).add (h47_int_abs_pow_exp 3 hkpos)
    refine this.congr (Filter.Eventually.of_forall fun T => ?_)
    simp only [Pi.add_apply, pow_zero, one_mul]; ring
  have hpt : ∀ T : ℝ, saddleGaussianTailWeight T * Real.exp (-k * |T|) ≤ g T := by
    intro T
    unfold saddleGaussianTailWeight
    simp only [hg]
    set x := |T| with hx
    have hx0 : 0 ≤ x := abs_nonneg T
    set y := (3 * k / 4) * x with hy
    have hy0 : 0 ≤ y := by positivity
    have e1 : 1 ≤ Real.exp y := Real.one_le_exp hy0
    have e2 : y ^ 3 / 6 ≤ Real.exp y := by
      have := Real.pow_div_factorial_le_exp y hy0 3
      simpa [Nat.factorial] using this
    have hy3 : 6 * x ^ 3 ≤ y ^ 3 := by
      have : (4.5 : ℝ) * x ≤ y := by rw [hy]; nlinarith
      have h45 : (0:ℝ) ≤ 4.5 * x := by positivity
      have := pow_le_pow_left₀ h45 this 3
      nlinarith [pow_nonneg hx0 3]
    have hpoly : 1 + x ^ 3 ≤ 2 * Real.exp y := by nlinarith
    have hsplit : Real.exp (-c * x) = Real.exp (-k * x) * Real.exp y := by
      rw [← Real.exp_add]; congr 1; rw [hy, hc]; ring
    rw [hsplit]
    have := mul_le_mul_of_nonneg_left hpoly (Real.exp_pos (-k * x)).le
    nlinarith [Real.exp_pos (-k * x)]
  have hSmeas : MeasurableSet (saddleGaussianTailSet R) := by
    unfold saddleGaussianTailSet
    exact measurableSet_le measurable_const measurable_abs
  have hstep1 : (∫ T in saddleGaussianTailSet R, saddleGaussianTailWeight T * Real.exp (-k * |T|)) ≤
      ∫ T in saddleGaussianTailSet R, g T :=
    MeasureTheory.setIntegral_mono_on hfint.integrableOn hgint.integrableOn hSmeas
      (fun T _ => hpt T)
  have hgnn : ∀ T, 0 ≤ g T := fun T => by simp only [hg]; positivity
  have hstep2 : (∫ T in saddleGaussianTailSet R, g T) ≤
      (∫ T in Iic (-R), g T) + ∫ T in Ici R, g T := by
    rw [← MeasureTheory.integral_indicator hSmeas, ← MeasureTheory.integral_indicator measurableSet_Iic,
      ← MeasureTheory.integral_indicator measurableSet_Ici,
      ← MeasureTheory.integral_add ((hgint.indicator measurableSet_Iic)) (hgint.indicator measurableSet_Ici)]
    apply MeasureTheory.integral_mono (hgint.indicator hSmeas)
      ((hgint.indicator measurableSet_Iic).add (hgint.indicator measurableSet_Ici))
    intro T
    simp only [Pi.add_apply, Set.indicator]
    unfold saddleGaussianTailSet
    simp only [Set.mem_setOf_eq, Set.mem_Iic, Set.mem_Ici]
    by_cases h1 : R ≤ |T|
    · rw [if_pos h1]
      rcases le_abs'.mp h1 with h | h
      · rw [if_pos h]; split_ifs <;> linarith [hgnn T]
      · rw [if_pos h]; split_ifs <;> linarith [hgnn T]
    · rw [if_neg h1]; split_ifs <;> linarith [hgnn T]
  have hIoi : (∫ T in Ioi R, g T) = 2 * (Real.exp (-c * R) / c) := by
    have : (∫ T in Ioi R, g T) = ∫ T in Ioi R, 2 * Real.exp (-c * T) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro T hT
      have hT0 : 0 ≤ T := le_trans hR (le_of_lt hT)
      simp only [hg, abs_of_nonneg hT0]
    rw [this, MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (by linarith) R]
    field_simp
  have hIic : (∫ T in Iic (-R), g T) = ∫ T in Ioi R, g T := by
    rw [← integral_comp_neg_Ioi]
    simp only [hg, abs_neg]
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi, hIic, hIoi] at hstep2
  calc _ ≤ _ := hstep1
    _ ≤ _ := hstep2
    _ = 2 * Real.exp (-(k / 4) * R) * (2 / (k / 4)) := by rw [hc]; ring

