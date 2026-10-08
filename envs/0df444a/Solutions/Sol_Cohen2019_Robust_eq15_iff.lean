-- Prove2me | solution 1 for Cohen2019.Robust.eq15_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T02:43:54.790483+00:00
-- url     : https://prove2.me/submissions/1285e2e7-6aa3-4678-bfec-bd4aeb97a275

import Mathlib
import Definitions.Def_Cohen2019_Robust_Phi

open MeasureTheory ProbabilityTheory in
theorem cohen727_phi_strictMono : StrictMono Cohen2019.Robust.Phi := by
  intro a b hab
  unfold Cohen2019.Robust.Phi
  have hv : (1 : NNReal) ≠ 0 := one_ne_zero
  have hpos : (gaussianReal 0 1) (Set.Ioc a b) ≠ 0 := by
    intro h
    have h2 := gaussianReal_absolutelyContinuous' (0 : ℝ) hv h
    rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at h2
    linarith
  have hm := (cdf (gaussianReal 0 1)).measure_Ioc a b
  rw [measure_cdf] at hm
  rw [hm] at hpos
  have : ¬ (cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a ≤ 0) := by
    intro hle; exact hpos (ENNReal.ofReal_eq_zero.mpr hle)
  linarith

open MeasureTheory ProbabilityTheory in
theorem solution (σ : ℝ) (hσ : 0 < σ) (pA pB : ℝ) (hpA0 : 0 < pA) (hpA1 : pA < 1)
    (hpB0 : 0 < pB) (hpB1 : pB < 1) (r : ℝ) :
    Cohen2019.Robust.Phi (Cohen2019.Robust.PhiInvReal pB + r / σ) < Cohen2019.Robust.Phi (Cohen2019.Robust.PhiInvReal pA - r / σ)
      ↔ r < σ / 2 * (Cohen2019.Robust.PhiInvReal pA - Cohen2019.Robust.PhiInvReal pB) := by
  rw [cohen727_phi_strictMono.lt_iff_lt]
  have key : r / σ * σ = r := div_mul_cancel₀ r hσ.ne'
  constructor
  · intro h
    nlinarith
  · intro h
    by_contra hc
    push_neg at hc
    nlinarith
