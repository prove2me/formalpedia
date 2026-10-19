-- Prove2me | solution 1 for CohnElkies.plusPolynomial_imaginary_re_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/c0c60357-30b6-49e2-ba41-29d56984118d

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
namespace CohnElkies
theorem _root_.solution {ε u : ℝ}
    (hε : 0 < ε) (hu : -1 < u) :
    0 < (plusPolynomial ε (Complex.I * (u : ℂ))).re := by
  have hs : 0 ≤ (1 - u) ^ 2 * (1 + u) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  rw [plusPolynomial_imaginary, Complex.ofReal_re]
  exact add_pos_of_pos_of_nonneg (beta_pos hε) hs
end CohnElkies
