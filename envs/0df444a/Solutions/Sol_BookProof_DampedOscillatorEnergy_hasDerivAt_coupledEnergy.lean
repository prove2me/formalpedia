-- Prove2me | solution 1 for BookProof.DampedOscillatorEnergy.hasDerivAt_coupledEnergy
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:46:17.1919+00:00
-- url     : https://prove2.me/submissions/b54755a4-f20a-4542-a16c-da86345c182b

-- Generated from ChapterDampedOscillatorEnergy.lean — solution of BookProof.DampedOscillatorEnergy.hasDerivAt_coupledEnergy
import Mathlib
import Definitions.Def_ChapterDampedOscillatorEnergy
open BookProof.DampedOscillatorEnergy




open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem solution {lam1 lam2 omega1 omega2 c : ℝ}
    {x1 x2 v1 v2 a1 a2 : ℝ → ℝ}
    (hx1 : ∀ t, HasDerivAt x1 (v1 t) t) (hx2 : ∀ t, HasDerivAt x2 (v2 t) t)
    (hv1 : ∀ t, HasDerivAt v1 (a1 t) t) (hv2 : ∀ t, HasDerivAt v2 (a2 t) t)
    (heq1 : ∀ t, a1 t + lam1 * v1 t + omega1 ^ 2 * x1 t - c * x2 t = 0)
    (heq2 : ∀ t, a2 t + lam2 * v2 t + omega2 ^ 2 * x2 t - c * x1 t = 0) (t : ℝ) :
    HasDerivAt (coupledEnergy omega1 omega2 c x1 x2 v1 v2)
      (-(lam1 * v1 t ^ 2) - lam2 * v2 t ^ 2) t := by

  have h1 : HasDerivAt (fun s => v1 s ^ 2 / 2) (v1 t * a1 t) t := by
    have h := ((hv1 t).pow 2).div_const 2
    convert h using 1 <;> first | rfl | ring
  have h2 : HasDerivAt (fun s => v2 s ^ 2 / 2) (v2 t * a2 t) t := by
    have h := ((hv2 t).pow 2).div_const 2
    convert h using 1 <;> first | rfl | ring
  have h3 : HasDerivAt (fun s => omega1 ^ 2 * x1 s ^ 2 / 2) (omega1 ^ 2 * (x1 t * v1 t)) t := by
    have h := (((hx1 t).pow 2).const_mul (omega1 ^ 2)).div_const 2
    convert h using 1 <;> first | rfl | ring
  have h4 : HasDerivAt (fun s => omega2 ^ 2 * x2 s ^ 2 / 2) (omega2 ^ 2 * (x2 t * v2 t)) t := by
    have h := (((hx2 t).pow 2).const_mul (omega2 ^ 2)).div_const 2
    convert h using 1 <;> first | rfl | ring
  have h5 : HasDerivAt (fun s => c * (x1 s * x2 s))
      (c * (v1 t * x2 t + x1 t * v2 t)) t := ((hx1 t).mul (hx2 t)).const_mul c
  have hsum := ((((h1.add h2).add h3).add h4).sub h5)
  have hrate : v1 t * a1 t + v2 t * a2 t + omega1 ^ 2 * (x1 t * v1 t)
      + omega2 ^ 2 * (x2 t * v2 t) - c * (v1 t * x2 t + x1 t * v2 t)
      = -(lam1 * v1 t ^ 2) - lam2 * v2 t ^ 2 := by
    have ha1 : a1 t = -(lam1 * v1 t) - omega1 ^ 2 * x1 t + c * x2 t := by linarith [heq1 t]
    have ha2 : a2 t = -(lam2 * v2 t) - omega2 ^ 2 * x2 t + c * x1 t := by linarith [heq2 t]
    rw [ha1, ha2]; ring
  have : HasDerivAt (coupledEnergy omega1 omega2 c x1 x2 v1 v2)
      (v1 t * a1 t + v2 t * a2 t + omega1 ^ 2 * (x1 t * v1 t)
        + omega2 ^ 2 * (x2 t * v2 t) - c * (v1 t * x2 t + x1 t * v2 t)) t := by
    exact hsum
  rwa [hrate] at this
