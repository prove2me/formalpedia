-- Prove2me | solution 1 for FirstPassageLinearTransport.mem_initialWindowGood_of_mem_extended_of_large
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:08:22.616259+00:00
-- url     : https://prove2.me/submissions/7b0ec64d-2e26-434b-bcda-5bbae326a7e0

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
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
    {r eta : ℝ} (p : StageSetup r eta) {n : ℕ}
    (hn : n ∈ extendedWindow p) (hlarge : p.M0 ≤ Nat.log 2 n) :
    n ∈ initialWindowGood eta := by
  rcases hn with hn | hn
  · exact hn
  · have hnlt : n < 2 ^ p.M0 := hn
    have hpow : 2 ^ p.M0 ≤ 2 ^ Nat.log 2 n :=
      Nat.pow_le_pow_right (by norm_num) hlarge
    have hnpos : 0 < n := by
      by_contra hzero
      have : n = 0 := Nat.eq_zero_of_not_pos hzero
      subst n
      have hlarge0 : p.M0 ≤ 0 := by simpa using hlarge
      have hbad := p.target_one_lt 0 hlarge0
      norm_num [targetScale] at hbad
    have hlogle : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hnpos.ne'
    omega
end FirstPassageLinearTransport
