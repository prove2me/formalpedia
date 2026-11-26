-- Prove2me | solution 1 for Eden.hasDerivAt_planarY_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:12:52.04732+00:00
-- url     : https://prove2.me/submissions/f404f941-570f-4627-9ad1-e3d41dbb0077

import Definitions.Def_Eden_ScalarCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Definitions.Def_Eden_PlanarFlow
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planar_radius_sq_of_pos
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_hasDerivAt_planarAmplitude_of_pos
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time


attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarY_origin

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (Ω : ℝ) {t x y : ℝ}
    (hD : 0 < radialDiscriminant t (x ^ 2 + y ^ 2))
    (hB : 0 < amplitudeSq t (x ^ 2 + y ^ 2)) :
    HasDerivAt (fun τ => planarY Ω τ x y)
      (q (planarX Ω t x y ^ 2 + planarY Ω t x y ^ 2) * planarY Ω t x y +
        Ω * planarX Ω t x y) t := by
  have hc := ((hasDerivAt_id t).const_mul Ω).cos
  have hsn := ((hasDerivAt_id t).const_mul Ω).sin
  have hrot := (hsn.const_mul x).add (hc.const_mul y)
  apply ((hasDerivAt_planarAmplitude_of_pos hD hB).mul hrot).congr_deriv
  rw [planar_radius_sq_of_pos Ω hD hB]
  dsimp [planarX, planarY]
  ring
end Eden
