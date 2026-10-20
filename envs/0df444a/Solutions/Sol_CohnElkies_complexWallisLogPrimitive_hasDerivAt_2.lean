-- Prove2me | solution 2 for CohnElkies.complexWallisLogPrimitive_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:27:59.766966+00:00
-- url     : https://prove2.me/submissions/36b35b1c-40ab-4f8c-a62d-a40542b9536a

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
    {z : ℂ} (hz : 0 < z.re)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun r : ℝ =>
        (z + (r : ℂ)) * Complex.log (z + (r : ℂ)) -
          (z + (r : ℂ)))
      (Complex.log (z + (s : ℂ))) s := by
  have hre : 0 < (z + (s : ℂ)).re := by simp; linarith [hs.1]
  have hslit : z + (s : ℂ) ∈ Complex.slitPlane := Or.inl hre
  have hne : z + (s : ℂ) ≠ 0 := fun h => by rw [h] at hre; simp at hre
  have h1 : HasDerivAt (fun r : ℝ => z + (r : ℂ)) 1 s := by
    simpa using ((hasDerivAt_id s).ofReal_comp).const_add z
  have h2 := (h1.mul (h1.clog_real hslit)).sub h1
  refine h2.congr_deriv ?_
  first
    | rw [one_mul, mul_one_div_cancel hne, add_sub_cancel_right]
    | simp [hne]
    | (field_simp; ring)

