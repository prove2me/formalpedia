-- Prove2me | solution 2 for CohnElkies.saddleSourceGaussianKernel_normalized_tail_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:34:46.493513+00:00
-- url     : https://prove2.me/submissions/f33f2776-b603-46c1-8ada-228ead7aa275

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution
    {ε ℓ u z : ℝ}
    (hℓ : 0 < ℓ)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u)
    (hz : 0 ≤ z)
    (hlarge : 12 ≤ ℓ * saddleSourceGaussianVariance ε ℓ u) :
    Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) *
      (∫ T : ℝ in saddleGaussianTailSet
        (z / Real.sqrt
          (ℓ * saddleSourceGaussianVariance ε ℓ u)),
          saddleSourceGaussianKernel ε ℓ u T) ≤
        4 * Real.sqrt (2 * Real.pi) *
          Real.exp (-(z ^ 2) / 8) := by
  set V := ℓ * saddleSourceGaussianVariance ε ℓ u with hVdef
  have hV0 : 0 < V := mul_pos hℓ hV
  set t0 := z / Real.sqrt V with ht0def
  have hK : ∀ T, saddleSourceGaussianKernel ε ℓ u T = Real.exp (-(V / 2) * T ^ 2) := fun T => rfl
  simp_rw [hK]
  have hmeas : MeasurableSet (saddleGaussianTailSet t0) :=
    measurableSet_le measurable_const measurable_abs
  have hg : Integrable (fun T : ℝ => Real.exp (-z ^ 2 / 4) * Real.exp (-(V / 4) * T ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity)).const_mul _
  have ht0 : 0 ≤ t0 := div_nonneg hz (Real.sqrt_nonneg _)
  have ht0sq : t0 ^ 2 = z ^ 2 / V := by rw [ht0def, div_pow, Real.sq_sqrt hV0.le]
  have h1 : ∫ T in saddleGaussianTailSet t0, Real.exp (-(V / 2) * T ^ 2) ≤
      ∫ T in saddleGaussianTailSet t0, Real.exp (-z ^ 2 / 4) * Real.exp (-(V / 4) * T ^ 2) := by
    refine setIntegral_mono_on (integrable_exp_neg_mul_sq (by positivity)).integrableOn
      hg.integrableOn hmeas (fun T hT => ?_)
    have hT' : t0 ≤ |T| := hT
    have hsq : t0 ^ 2 ≤ T ^ 2 := by rw [← sq_abs T]; exact pow_le_pow_left₀ ht0 hT' 2
    rw [ht0sq] at hsq
    have := (div_le_iff₀ hV0).1 hsq
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  have h2 : ∫ T in saddleGaussianTailSet t0, Real.exp (-z ^ 2 / 4) * Real.exp (-(V / 4) * T ^ 2) ≤
      ∫ T, Real.exp (-z ^ 2 / 4) * Real.exp (-(V / 4) * T ^ 2) :=
    setIntegral_le_integral hg (Eventually.of_forall fun T => by positivity)
  have h3 : ∫ T, Real.exp (-z ^ 2 / 4) * Real.exp (-(V / 4) * T ^ 2) =
      Real.exp (-z ^ 2 / 4) * Real.sqrt (Real.pi / (V / 4)) := by
    rw [integral_const_mul, integral_gaussian]
  calc Real.sqrt V * ∫ T in saddleGaussianTailSet t0, Real.exp (-(V / 2) * T ^ 2)
      ≤ Real.sqrt V * (Real.exp (-z ^ 2 / 4) * Real.sqrt (Real.pi / (V / 4))) :=
        mul_le_mul_of_nonneg_left (h1.trans (h2.trans h3.le)) (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt Real.pi * Real.exp (-z ^ 2 / 4) := by
        rw [← mul_assoc, mul_comm (Real.sqrt V) (Real.exp _), mul_assoc, ← Real.sqrt_mul hV0.le,
          show V * (Real.pi / (V / 4)) = 2 ^ 2 * Real.pi by field_simp; ring,
          Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
        ring
    _ ≤ 4 * Real.sqrt (2 * Real.pi) * Real.exp (-(z ^ 2) / 8) := by
        have a1 : Real.sqrt Real.pi ≤ Real.sqrt (2 * Real.pi) :=
          Real.sqrt_le_sqrt (by linarith [Real.pi_pos])
        have a2 : Real.exp (-z ^ 2 / 4) ≤ Real.exp (-(z ^ 2) / 8) :=
          Real.exp_le_exp.2 (by nlinarith [sq_nonneg z])
        have := mul_le_mul a1 a2 (Real.exp_pos _).le (Real.sqrt_nonneg _)
        nlinarith [Real.sqrt_nonneg Real.pi, Real.exp_pos (-z ^ 2 / 4)]

