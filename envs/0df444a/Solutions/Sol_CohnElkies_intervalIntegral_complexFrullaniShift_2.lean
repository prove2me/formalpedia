-- Prove2me | solution 2 for CohnElkies.intervalIntegral_complexFrullaniShift
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:05:37.011518+00:00
-- url     : https://prove2.me/submissions/dc60493f-4ae8-43f2-b638-194baf4c697f

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
    (z : ℂ) {x : ℝ} (hx : x ≠ 0) :
    (∫ s in (0 : ℝ)..1,
      complexFrullaniKernel (z + (s : ℂ)) 1 x) =
      complexWallisPhaseKernel z x := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have h0 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := fun s => by
    simpa using (hasDerivAt_id s).ofReal_comp
  have hd : ∀ s : ℝ, HasDerivAt
      (fun s : ℝ => -Complex.exp (-(z + (s : ℂ)) * (x : ℂ)) / (x : ℂ) ^ 2 -
        (s : ℂ) * Complex.exp (-(x : ℂ)) / (x : ℂ))
      (complexFrullaniKernel (z + (s : ℂ)) 1 x) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => -(z + (s : ℂ)) * (x : ℂ)) (-(x : ℂ)) s := by
      have := ((h0 s).const_add z).neg.mul_const (x : ℂ)
      exact this.congr_deriv (by ring)
    have h2 := ((h1.cexp.neg).div_const ((x : ℂ) ^ 2)).sub
      (((h0 s).mul_const (Complex.exp (-(x : ℂ)))).div_const (x : ℂ))
    refine h2.congr_deriv ?_
    unfold complexFrullaniKernel
    rw [show -(1:ℂ) * (x:ℂ) = -(x:ℂ) by ring]
    field_simp
    try ring
  have hc : Continuous (fun s : ℝ => complexFrullaniKernel (z + (s : ℂ)) 1 x) := by
    unfold complexFrullaniKernel; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) (hc.intervalIntegrable _ _)]
  have he : Complex.exp (-(z + 1) * (x : ℂ)) = Complex.exp (-z * (x : ℂ)) * Complex.exp (-(x : ℂ)) := by
    rw [← Complex.exp_add]; ring_nf
  simp only [Complex.ofReal_one, Complex.ofReal_zero, add_zero, one_mul, zero_mul, sub_zero]
  rw [he]
  unfold complexWallisPhaseKernel
  field_simp
  try ring

