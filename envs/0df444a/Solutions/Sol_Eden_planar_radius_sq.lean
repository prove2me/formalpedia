-- Prove2me | solution 1 for Eden.planar_radius_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:06:18.094912+00:00
-- url     : https://prove2.me/submissions/a443665a-205a-4341-9918-9aa7a8b81f1d

import Definitions.Def_Eden_ScalarCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Definitions.Def_Eden_PlanarFlow
import Theorems.Thm_Eden_planar_radius_sq_of_pos
import Theorems.Thm_Eden_amplitudeSq_pos
import Theorems.Thm_Eden_radialDiscriminant_pos


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (x y : ℝ) :
    planarX Ω t x y ^ 2 + planarY Ω t x y ^ 2 =
      squaredRadiusEvolution t (x ^ 2 + y ^ 2) :=
  planar_radius_sq_of_pos Ω (radialDiscriminant_pos ht _)
    (amplitudeSq_pos ht (add_nonneg (sq_nonneg x) (sq_nonneg y)))
end Eden
