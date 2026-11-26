-- Prove2me | solution 1 for FirstPassageLinearTransport.collatzBallotOuterLength_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:57:11.993387+00:00
-- url     : https://prove2.me/submissions/30c4e9ca-778c-40c8-ba99-22630a17fdf7

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
    (m : ℝ) / 8 ≤ collatzBallotOuterLength m := by
  have hle : m < 4 * (m / 4 + 1) :=
    Nat.lt_mul_div_succ m (by omega : 0 < 4)
  have hnat : m ≤ 8 * (m / 4) := by omega
  have hreal : (m : ℝ) ≤ 8 * ((m / 4 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  simp only [collatzBallotOuterLength]
  norm_num at hreal ⊢
  linarith
end FirstPassageLinearTransport
