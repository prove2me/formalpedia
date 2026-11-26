-- Prove2me | solution 1 for FirstPassageLinearTransport.terminal_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:25:52.516485+00:00
-- url     : https://prove2.me/submissions/0a9a0939-e5b6-4da5-97a4-e31df8449fb4

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_centralOrbitScale_pos
import Theorems.Thm_FirstPassageLinearTransport_log_two_eq_of_mem_dyadicShell
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
theorem _root_.solution {r eta : ℝ} (p : StageSetup r eta)
    {M n : ℕ} (hM : p.M0 ≤ M) (hnShell : n ∈ dyadicShell M)
    (hnGood : n ∈ initialWindowGood eta) :
    orbit M n ≤ targetScale r M := by
  have hlog := log_two_eq_of_mem_dyadicShell hnShell
  have henv := hnGood M (by simp [hlog])
  have hnUpperNat : n < 2 ^ (M + 1) := (mem_dyadicShell.mp hnShell).2
  have hnUpper : (n : ℝ) ≤ (2 : ℝ) ^ (M + 1) := by
    exact_mod_cast hnUpperNat.le
  have hpow :
      (n : ℝ) ^ (1 + eta) ≤ ((2 : ℝ) ^ (M + 1)) ^ (1 + eta) :=
    Real.rpow_le_rpow (by positivity) hnUpper (by linarith [p.eta_pos])
  have hscale : 0 ≤ centralOrbitScale M := (centralOrbitScale_pos M).le
  have hreal :
      (orbit M n : ℝ) ≤ targetScale r M :=
    henv.2.trans ((mul_le_mul_of_nonneg_left hpow hscale).trans
      (p.terminal_budget M hM))
  exact_mod_cast hreal
end FirstPassageLinearTransport
