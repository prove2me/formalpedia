-- Prove2me | solution 2 for CohnElkies.saddleGaussian_cubic_tail_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:35:50.408624+00:00
-- url     : https://prove2.me/submissions/c50f2421-9c94-4fa0-b732-11245f2e178b

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


theorem solution
    {k R : ℝ} (hk : 6 ≤ k) (hR : 0 ≤ R) :
    (∫ T : ℝ in saddleGaussianTailSet R,
      saddleGaussianTailWeight T *
        Real.exp (-k * T ^ 2)) ≤
      2 * Real.exp (-(k / 4) * R ^ 2) *
        Real.sqrt (Real.pi / (k / 4)) := by
  have hk4 : 0 < k / 4 := by linarith
  have hgint : Integrable (fun T : ℝ => 2 * Real.exp (-(k / 4) * R ^ 2) * Real.exp (-(k / 4) * T ^ 2)) :=
    (integrable_exp_neg_mul_sq hk4).const_mul _
  have hSmeas : MeasurableSet (saddleGaussianTailSet R) :=
    measurableSet_le measurable_const measurable_abs
  have hbound : ∀ T ∈ saddleGaussianTailSet R,
      saddleGaussianTailWeight T * Real.exp (-k * T ^ 2) ≤
        2 * Real.exp (-(k / 4) * R ^ 2) * Real.exp (-(k / 4) * T ^ 2) := by
    intro T hT
    have hT' : R ≤ |T| := hT
    unfold saddleGaussianTailWeight
    have ht := abs_nonneg T
    have hT2 : T ^ 2 = |T| ^ 2 := (sq_abs T).symm
    have hRt : R ^ 2 ≤ T ^ 2 := by rw [hT2]; exact pow_le_pow_left₀ hR hT' 2
    have hq := Real.quadratic_le_exp_of_nonneg (x := 3 * T ^ 2) (by positivity)
    have hpoly : 1 + |T| ^ 3 ≤ 2 * Real.exp (3 * T ^ 2) := by
      rw [hT2] at hq ⊢
      nlinarith [mul_nonneg (sq_nonneg |T|) (sq_nonneg (|T| - 1)), sq_nonneg |T|]
    have e1 : Real.exp (-k * T ^ 2) ≤
        Real.exp (-(3 * T ^ 2)) * Real.exp (-(k / 4) * R ^ 2) * Real.exp (-(k / 4) * T ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg T]
    have e2 : (1 + |T| ^ 3) * Real.exp (-(3 * T ^ 2)) ≤ 2 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
      exact hpoly
    have hw : 0 ≤ 1 + |T| ^ 3 := by positivity
    calc (1 + |T| ^ 3) * Real.exp (-k * T ^ 2)
        ≤ (1 + |T| ^ 3) * (Real.exp (-(3 * T ^ 2)) * Real.exp (-(k / 4) * R ^ 2) *
            Real.exp (-(k / 4) * T ^ 2)) := mul_le_mul_of_nonneg_left e1 hw
      _ = ((1 + |T| ^ 3) * Real.exp (-(3 * T ^ 2))) * Real.exp (-(k / 4) * R ^ 2) *
            Real.exp (-(k / 4) * T ^ 2) := by ring
      _ ≤ 2 * Real.exp (-(k / 4) * R ^ 2) * Real.exp (-(k / 4) * T ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_right e2 (Real.exp_pos _).le
  have hfmeas : Measurable (fun T : ℝ => saddleGaussianTailWeight T * Real.exp (-k * T ^ 2)) := by
    unfold saddleGaussianTailWeight; fun_prop
  have hfint : IntegrableOn (fun T : ℝ => saddleGaussianTailWeight T * Real.exp (-k * T ^ 2))
      (saddleGaussianTailSet R) := by
    refine Integrable.mono' hgint.integrableOn hfmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hSmeas] with T hT
    have hw : 0 ≤ saddleGaussianTailWeight T := by unfold saddleGaussianTailWeight; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hbound T hT
  calc (∫ T : ℝ in saddleGaussianTailSet R, saddleGaussianTailWeight T * Real.exp (-k * T ^ 2))
      ≤ ∫ T : ℝ in saddleGaussianTailSet R,
          2 * Real.exp (-(k / 4) * R ^ 2) * Real.exp (-(k / 4) * T ^ 2) :=
        setIntegral_mono_on hfint hgint.integrableOn hSmeas hbound
    _ ≤ ∫ T : ℝ, 2 * Real.exp (-(k / 4) * R ^ 2) * Real.exp (-(k / 4) * T ^ 2) :=
        setIntegral_le_integral hgint (Filter.Eventually.of_forall fun T => by positivity)
    _ = 2 * Real.exp (-(k / 4) * R ^ 2) * Real.sqrt (Real.pi / (k / 4)) := by
        rw [integral_const_mul, integral_gaussian]

