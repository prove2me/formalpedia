-- Prove2me | solution 1 for CohnElkies.rpow_two_pow_inv_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/910ffdf1-0f68-4674-97ca-a6f1ba48b303

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Nat Topology
namespace CohnElkies
theorem _root_.solution {d : ℕ} (hd : 0 < d) :
    ((2 : ℝ) ^ d) ^ ((d : ℝ)⁻¹) = 2 := by
  have hdreal : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  calc
    ((2 : ℝ) ^ d) ^ ((d : ℝ)⁻¹) =
        ((2 : ℝ) ^ (d : ℝ)) ^ ((d : ℝ)⁻¹) := by
          rw [Real.rpow_natCast]
    _ = (2 : ℝ) ^ ((d : ℝ) * (d : ℝ)⁻¹) := by
          rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ = 2 := by rw [mul_inv_cancel₀ hdreal, Real.rpow_one]
end CohnElkies
