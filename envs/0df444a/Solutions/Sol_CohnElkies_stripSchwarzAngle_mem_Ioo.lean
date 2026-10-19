-- Prove2me | solution 1 for CohnElkies.stripSchwarzAngle_mem_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/ff59baae-bde4-41c9-a614-40934a7c8ac7

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) :
    0 < Real.pi * (z.im + ℓ) / (2 * ℓ) ∧
      Real.pi * (z.im + ℓ) / (2 * ℓ) < Real.pi := by
  change -ℓ < z.im ∧ z.im < ℓ at hz
  constructor
  · exact div_pos (mul_pos Real.pi_pos (by linarith))
      (mul_pos (by norm_num) hℓ)
  · apply (div_lt_iff₀ (mul_pos (by norm_num) hℓ)).2
    nlinarith [mul_pos Real.pi_pos (show 0 < ℓ - z.im by linarith)]
end CohnElkies
