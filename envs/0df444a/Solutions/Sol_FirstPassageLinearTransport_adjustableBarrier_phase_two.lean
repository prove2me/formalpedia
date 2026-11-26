-- Prove2me | solution 1 for FirstPassageLinearTransport.adjustableBarrier_phase_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:40:28.052751+00:00
-- url     : https://prove2.me/submissions/503246b4-1c1d-4bfb-a2d2-c1c6988513b0

import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
import Theorems.Thm_FirstPassageLinearTransport_three_rpow_adjustableBarrierHeight
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {lambda t : ℝ} {M n : ℕ}
    (ht : 0 ≤ t)
    (hstartup : 1 ≤ (1 - lambda) * t * (M : ℝ))
    (hnShell : n ∈ dyadicShell M) :
    2 * (3 : ℝ) ^ adjustableBarrierHeight lambda t M ≤ (n : ℝ) ^ t := by
  have hnLowerNat : 2 ^ M ≤ n := (mem_dyadicShell.mp hnShell).1
  have hnLower : (2 : ℝ) ^ M ≤ n := by exact_mod_cast hnLowerNat
  rw [three_rpow_adjustableBarrierHeight]
  calc
    2 * (2 : ℝ) ^ (lambda * t * (M : ℝ)) =
        (2 : ℝ) ^ (1 + lambda * t * (M : ℝ)) := by
      calc
        2 * (2 : ℝ) ^ (lambda * t * (M : ℝ)) =
            (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (lambda * t * (M : ℝ)) := by
              norm_num
        _ = (2 : ℝ) ^ (1 + lambda * t * (M : ℝ)) := by
              rw [Real.rpow_add (by norm_num)]
    _ ≤ (2 : ℝ) ^ (t * (M : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hsplit :
          (1 - lambda) * t * (M : ℝ) =
            t * (M : ℝ) - lambda * t * (M : ℝ) := by
        ring
      rw [hsplit] at hstartup
      linarith
    _ = ((2 : ℝ) ^ M) ^ t := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    _ ≤ (n : ℝ) ^ t := Real.rpow_le_rpow (by positivity) hnLower ht
end FirstPassageLinearTransport
