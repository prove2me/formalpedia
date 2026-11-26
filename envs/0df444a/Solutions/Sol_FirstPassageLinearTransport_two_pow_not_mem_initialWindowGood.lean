-- Prove2me | solution 1 for FirstPassageLinearTransport.two_pow_not_mem_initialWindowGood
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:39:30.317795+00:00
-- url     : https://prove2.me/submissions/2fe178be-5e05-453f-8690-1418767ad2fb

import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierCore
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_orbit_two_pow
import Theorems.Thm_FirstPassageLinearTransport_centralScale_mul_twoPow_eq
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSourcesAtTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSources
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSourcesAtTimes
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero


attribute [local simp] FirstPassageLinearTransport.StageSetup.lowerTolerance_M0

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {q : ℕ} (hq : 1 ≤ q) {t : ℝ} (htA : t < a0) :
    2 ^ q ∉ initialWindowGood t := by
  intro hgood
  have hlog : Nat.log 2 (2 ^ q) = q := Nat.log_pow (by norm_num) q
  have henv := hgood q (by simp [hlog])
  have hlower :
      centralOrbitScale q * (((2 ^ q : ℕ) : ℝ) ^ (1 - t)) ≤ 1 := by
    simpa [orbit_two_pow] using henv.1
  rw [centralScale_mul_twoPow_eq] at hlower
  have hexp : 0 < (a0 - t) * (q : ℝ) := by
    exact mul_pos (sub_pos.mpr htA) (by exact_mod_cast hq)
  exact (not_lt_of_ge hlower) (Real.one_lt_rpow (by norm_num) hexp)
end FirstPassageLinearTransport
