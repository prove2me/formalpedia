-- Prove2me | solution 1 for CohnElkies.saddleNegativeFrequencyMajorant_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/bd01b975-0c9d-40a6-bd56-51a54558f44d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_integrable_abs_pow_mul_exp_neg_mul_abs

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {ε : ℝ} (hε : 0 < ε) :
    Integrable (saddleNegativeFrequencyMajorant ε) := by
  have hrate : 0 < ε * Real.pi := mul_pos hε Real.pi_pos
  have h0 := integrable_abs_pow_mul_exp_neg_mul_abs 0 hrate
  have h1 := integrable_abs_pow_mul_exp_neg_mul_abs 1 hrate
  have h2 := integrable_abs_pow_mul_exp_neg_mul_abs 2 hrate
  have h3 := integrable_abs_pow_mul_exp_neg_mul_abs 3 hrate
  have hsum := h0.add
    ((h1.const_mul 3).add
      ((h2.const_mul 3).add h3))
  apply hsum.congr
  filter_upwards [] with s
  unfold saddleNegativeFrequencyMajorant
  simp only [Pi.add_apply, pow_zero, pow_one]
  ring_nf
end CohnElkies
