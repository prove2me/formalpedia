-- Prove2me | solution 1 for FirstPassageLinearTransport.normalized_multiplicativeHitCount_le_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:59:42.785269+00:00
-- url     : https://prove2.me/submissions/2c251ef1-6c8b-4249-b4f3-f6c87ef75dec

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_multiplicativeHitCount_mul_le
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
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {u : ℝ} (hu : 0 < u) (M : ℕ) :
    (multiplicativeHitCount u M 1 : ℝ) / (2 : ℝ) ^ M ≤ u⁻¹ := by
  have htree := multiplicativeHitCount_mul_le u M 1 (by norm_num)
  have hpow : 0 < (2 : ℝ) ^ M := by positivity
  rw [div_le_iff₀ hpow]
  have hcount :
      (multiplicativeHitCount u M 1 : ℝ) ≤ (2 : ℝ) ^ M / u :=
    (le_div_iff₀ hu).2 (by simpa using htree)
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hcount
end FirstPassageLinearTransport
