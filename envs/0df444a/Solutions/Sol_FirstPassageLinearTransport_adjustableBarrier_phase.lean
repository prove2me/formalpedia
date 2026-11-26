-- Prove2me | solution 1 for FirstPassageLinearTransport.adjustableBarrier_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:40:22.167489+00:00
-- url     : https://prove2.me/submissions/a6ae788d-817f-4296-b379-78a47465a15a

import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
import Theorems.Thm_FirstPassageLinearTransport_three_rpow_adjustableBarrierHeight
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {lambda t : ℝ} {M n : ℕ}
    (hlambda1 : lambda ≤ 1)
    (ht : 0 ≤ t) (hnShell : n ∈ dyadicShell M) :
    (3 : ℝ) ^ adjustableBarrierHeight lambda t M ≤ (n : ℝ) ^ t := by
  have hnLowerNat : 2 ^ M ≤ n := (mem_dyadicShell.mp hnShell).1
  have hnLower : (2 : ℝ) ^ M ≤ n := by exact_mod_cast hnLowerNat
  rw [three_rpow_adjustableBarrierHeight]
  calc
    (2 : ℝ) ^ (lambda * t * (M : ℝ)) ≤
        (2 : ℝ) ^ (t * (M : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hM : (0 : ℝ) ≤ M := by positivity
      have hlt : lambda * t ≤ 1 * t :=
        mul_le_mul_of_nonneg_right hlambda1 ht
      exact mul_le_mul_of_nonneg_right (by simpa using hlt) hM
    _ = ((2 : ℝ) ^ M) ^ t := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    _ ≤ (n : ℝ) ^ t := Real.rpow_le_rpow (by positivity) hnLower ht
end FirstPassageLinearTransport
