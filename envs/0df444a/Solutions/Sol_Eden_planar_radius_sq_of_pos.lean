-- Prove2me | solution 1 for Eden.planar_radius_sq_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:48.607523+00:00
-- url     : https://prove2.me/submissions/717cda6c-1e0e-4e06-92fe-38bc54e14598

import Definitions.Def_Eden_ScalarCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Definitions.Def_Eden_PlanarFlow
import Theorems.Thm_Eden_mul_amplitudeSq_of_discriminant_pos


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (Ω : ℝ) {t x y : ℝ}
    (hD : 0 < radialDiscriminant t (x ^ 2 + y ^ 2))
    (hB : 0 < amplitudeSq t (x ^ 2 + y ^ 2)) :
    planarX Ω t x y ^ 2 + planarY Ω t x y ^ 2 =
      squaredRadiusEvolution t (x ^ 2 + y ^ 2) := by
  have hsq : planarAmplitude t (x ^ 2 + y ^ 2) ^ 2 = amplitudeSq t (x ^ 2 + y ^ 2) :=
    Real.sq_sqrt hB.le
  calc
    planarX Ω t x y ^ 2 + planarY Ω t x y ^ 2 =
        (x ^ 2 + y ^ 2) * planarAmplitude t (x ^ 2 + y ^ 2) ^ 2 *
          (Real.sin (Ω * t) ^ 2 + Real.cos (Ω * t) ^ 2) := by
      unfold planarX planarY
      ring
    _ = (x ^ 2 + y ^ 2) * amplitudeSq t (x ^ 2 + y ^ 2) := by
      rw [Real.sin_sq_add_cos_sq, mul_one, hsq]
    _ = squaredRadiusEvolution t (x ^ 2 + y ^ 2) := mul_amplitudeSq_of_discriminant_pos hD
end Eden
