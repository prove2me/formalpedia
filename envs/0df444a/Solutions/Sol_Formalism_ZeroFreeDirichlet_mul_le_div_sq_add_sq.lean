-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.mul_le_div_sq_add_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:44:08.513888+00:00
-- url     : https://prove2.me/submissions/a17ceca7-3635-45b7-9f97-081596dbc019

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_RealSmallTOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (T X G : ℝ) (hT : 0 < T) (h1 : 1 ≤ T * X) (h2 : T * X ≤ 11 / 10)
    (h3 : |T * G| ≤ 1 / 10) : 4 / 5 * T ≤ X / (X ^ 2 + G ^ 2) := by
  have hX : 0 < X := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  have hv : (T * G) ^ 2 ≤ 1 / 100 := by
    have := sq_abs (T * G)
    nlinarith [abs_nonneg (T * G)]
  have key : T * (4 / 5 * T * (X ^ 2 + G ^ 2)) ≤ T * X := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ T * X) (by linarith : 0 ≤ 11 / 10 - T * X)]
  have := le_of_mul_le_mul_left key hT
  rw [le_div_iff₀ (add_pos_of_pos_of_nonneg (pow_pos hX 2) (sq_nonneg G))]
  exact this
end Formalism.ZeroFreeDirichlet
