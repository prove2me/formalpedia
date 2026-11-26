-- Prove2me | solution 1 for Eden.hasDerivAt_planarY
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:13:48.978213+00:00
-- url     : https://prove2.me/submissions/ba94317e-3b67-41f7-a7f1-4fee19eb2701

import Definitions.Def_Eden_ScalarCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Definitions.Def_Eden_PlanarFlow
import Theorems.Thm_Eden_hasDerivAt_planarY_of_pos
import Theorems.Thm_Eden_amplitudeSq_pos
import Theorems.Thm_Eden_radialDiscriminant_pos


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (x y : ℝ) :
    HasDerivAt (fun τ => planarY Ω τ x y)
      (q (planarX Ω t x y ^ 2 + planarY Ω t x y ^ 2) * planarY Ω t x y +
        Ω * planarX Ω t x y) t :=
  hasDerivAt_planarY_of_pos Ω (radialDiscriminant_pos ht _)
    (amplitudeSq_pos ht (add_nonneg (sq_nonneg x) (sq_nonneg y)))
end Eden
