-- Prove2me | solution 1 for FirstPassageLinearTransport.collatzBallotMiddleLength_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:57:17.60957+00:00
-- url     : https://prove2.me/submissions/ac4c8f1b-bc2a-4803-b709-5087685b918e

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
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
theorem _root_.solution {m : ℕ} (hm : 8 ≤ m) :
    (m : ℝ) / 4 ≤ collatzBallotMiddleLength m := by
  simp only [collatzBallotMiddleLength, collatzBallotOuterLength]
  have h : m / 4 * 4 ≤ m := Nat.div_mul_le_self m 4
  have hnat : m ≤ 4 * (m - 2 * (m / 4)) := by omega
  have hreal : (m : ℝ) ≤ 4 * ((m - 2 * (m / 4) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  norm_num at hreal ⊢
  linarith
end FirstPassageLinearTransport
