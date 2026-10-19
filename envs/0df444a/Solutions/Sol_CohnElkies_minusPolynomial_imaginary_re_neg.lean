-- Prove2me | solution 1 for CohnElkies.minusPolynomial_imaginary_re_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/22012ff6-a1de-4034-bfbd-3767b3a09ebe

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
    (hε : 0 < ε) (hu : 1 + ε / 4 ≤ u) :
    (minusPolynomial ε (Complex.I * (u : ℂ))).re < 0 := by
  rw [minusPolynomial_imaginary, Complex.ofReal_re]
  have huone : 1 ≤ u := by linarith
  have hs : (4 : ℝ) ≤ (1 + u) ^ 2 := by
    nlinarith [sq_nonneg (u - 1)]
  have ht : ε / 4 ≤ u - 1 := by linarith
  have hproduct : ε ≤ (u - 1) * (1 + u) ^ 2 := by
    calc
      ε = (ε / 4) * 4 := by ring
      _ ≤ (u - 1) * (1 + u) ^ 2 :=
        mul_le_mul ht hs (by norm_num) (by linarith)
  unfold beta
  nlinarith
end CohnElkies
