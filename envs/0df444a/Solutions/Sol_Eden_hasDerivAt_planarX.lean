-- Prove2me | solution 1 for Eden.hasDerivAt_planarX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:13:47.751836+00:00
-- url     : https://prove2.me/submissions/445fec5b-c529-4245-bd78-b7fe0fe8e980

import Definitions.Def_Eden_ScalarCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Definitions.Def_Eden_PlanarFlow
import Theorems.Thm_Eden_hasDerivAt_planarX_of_pos
import Theorems.Thm_Eden_amplitudeSq_pos
import Theorems.Thm_Eden_radialDiscriminant_pos


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (x y : ℝ) :
    HasDerivAt (fun τ => planarX Ω τ x y)
      (q (planarX Ω t x y ^ 2 + planarY Ω t x y ^ 2) * planarX Ω t x y -
        Ω * planarY Ω t x y) t :=
  hasDerivAt_planarX_of_pos Ω (radialDiscriminant_pos ht _)
    (amplitudeSq_pos ht (add_nonneg (sq_nonneg x) (sq_nonneg y)))
end Eden
