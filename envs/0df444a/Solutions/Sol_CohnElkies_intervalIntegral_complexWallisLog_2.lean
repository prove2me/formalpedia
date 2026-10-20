-- Prove2me | solution 2 for CohnElkies.intervalIntegral_complexWallisLog
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:51:01.110877+00:00
-- url     : https://prove2.me/submissions/c8ee7e68-65de-484c-a6ff-79766c2e22cf

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
    {z : ℂ} (hz : 0 < z.re) :
    (∫ s in (0 : ℝ)..1,
      Complex.log (z + (s : ℂ))) =
      (z + 1) * Complex.log (z + 1) -
        z * Complex.log z - 1 := by
  have hslit : ∀ s : ℝ, 0 ≤ s → z + (s : ℂ) ∈ Complex.slitPlane := by
    intro s hs
    rw [Complex.mem_slitPlane_iff]
    left; simp; linarith
  have hderiv : ∀ s ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun s : ℝ => (z + (s : ℂ)) * Complex.log (z + (s : ℂ)) - (z + (s : ℂ)))
      (Complex.log (z + (s : ℂ))) s := by
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    have h1 : HasDerivAt (fun s : ℝ => z + (s : ℂ)) 1 s := by
      simpa using ((hasDerivAt_id (s : ℂ)).comp_ofReal).const_add z
    have h2 := (h1.clog_real (hslit s hs.1))
    have h3 := (h1.mul h2).sub h1
    have hne : z + (s : ℂ) ≠ 0 := Complex.slitPlane_ne_zero (hslit s hs.1)
    have e : 1 * Complex.log (z + (s : ℂ)) + (z + (s : ℂ)) * (1 / (z + (s : ℂ))) - 1 = Complex.log (z + (s : ℂ)) := by
      rw [mul_one_div_cancel hne]; ring
    rw [e] at h3; exact h3
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · push_cast
    rw [add_zero]; ring
  · apply ContinuousOn.intervalIntegrable
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    apply ContinuousAt.continuousWithinAt
    exact ContinuousAt.clog (f := fun x : ℝ => z + (x : ℂ)) (by fun_prop) (hslit s hs.1)

