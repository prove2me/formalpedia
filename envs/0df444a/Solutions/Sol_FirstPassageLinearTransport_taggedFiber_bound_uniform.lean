-- Prove2me | solution 1 for FirstPassageLinearTransport.taggedFiber_bound_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:40:08.88404+00:00
-- url     : https://prove2.me/submissions/d2006bd9-fc8e-4c79-adc5-2ecabbf10137

import Definitions.Def_FirstPassageLinearTransport_FirstPassage
import Definitions.Def_FirstPassageLinearTransport_Transport
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_taggedFiber_bound
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
namespace FirstPassageLinearTransport
theorem _root_.solution {M Y H h y : ℕ}
    (hY : 0 < Y) (hpos : 1 ≤ h) (hhH : h ≤ H)
    (hHY : (H : ℚ) / (2 * (Y : ℚ)) ≤ 1 / 3)
    (hYM : Y < 2 ^ M) :
    ((taggedFiber M Y h y).card : ℚ) ≤
      (5 / 2 : ℚ) * (H : ℚ) * (2 : ℚ) ^ M / (Y : ℚ) := by
  have hYQ : (0 : ℚ) < (Y : ℚ) := by exact_mod_cast hY
  have htwoY : (0 : ℚ) < 2 * (Y : ℚ) := by positivity
  have hhHq : (h : ℚ) ≤ (H : ℚ) := by exact_mod_cast hhH
  have hsmall : (h : ℚ) / (2 * (Y : ℚ)) ≤ 1 / 3 := by
    exact (div_le_div_of_nonneg_right hhHq (by positivity)).trans hHY
  have hscaled := (div_le_iff₀ htwoY).mp hHY
  have hHupper : (H : ℚ) ≤ 2 * (Y : ℚ) / 3 := by
    nlinarith
  have hden : (0 : ℚ) < 2 * (Y : ℚ) - (h : ℚ) := by
    nlinarith
  have hdenLower : (4 / 3 : ℚ) * (Y : ℚ) ≤
      2 * (Y : ℚ) - (h : ℚ) := by
    nlinarith
  have hratioCross :
      (2 * (h : ℚ)) * (Y : ℚ) ≤
        ((3 / 2 : ℚ) * (H : ℚ)) *
          (2 * (Y : ℚ) - (h : ℚ)) := by
    have hleft :
        (2 * (h : ℚ)) * (Y : ℚ) ≤
          (2 * (H : ℚ)) * (Y : ℚ) := by
      exact mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    have hright :
        (2 * (H : ℚ)) * (Y : ℚ) ≤
          ((3 / 2 : ℚ) * (H : ℚ)) *
            (2 * (Y : ℚ) - (h : ℚ)) := by
      have := mul_le_mul_of_nonneg_left hdenLower
        (show 0 ≤ (3 / 2 : ℚ) * (H : ℚ) by positivity)
      nlinarith
    exact hleft.trans hright
  have hratio :
      (2 * (h : ℚ)) / (2 * (Y : ℚ) - (h : ℚ)) ≤
        ((3 / 2 : ℚ) * (H : ℚ)) / (Y : ℚ) := by
    exact (div_le_div_iff₀ hden hYQ).2 hratioCross
  have hpowNonneg : (0 : ℚ) ≤ (2 : ℚ) ^ M := by positivity
  have hterm :
      2 * (h : ℚ) * (2 : ℚ) ^ M /
          (2 * (Y : ℚ) - (h : ℚ)) ≤
        (3 / 2 : ℚ) * (H : ℚ) * (2 : ℚ) ^ M / (Y : ℚ) := by
    have := mul_le_mul_of_nonneg_right hratio hpowNonneg
    simpa [div_mul_eq_mul_div, mul_assoc] using this
  have hYMq : (Y : ℚ) < (2 : ℚ) ^ M := by exact_mod_cast hYM
  have hone : (1 : ℚ) ≤ (H : ℚ) * (2 : ℚ) ^ M / (Y : ℚ) := by
    apply (le_div_iff₀ hYQ).2
    have hHone : (1 : ℚ) ≤ (H : ℚ) := by exact_mod_cast (hpos.trans hhH)
    have hPowLe : (2 : ℚ) ^ M ≤ (H : ℚ) * (2 : ℚ) ^ M := by
      simpa using mul_le_mul_of_nonneg_right hHone hpowNonneg
    simpa using (le_of_lt hYMq).trans hPowLe
  have hraw := taggedFiber_bound (M := M) (Y := Y) (h := h) (y := y) hY hsmall
  have hterm' :
      2 * (h : ℚ) * (2 : ℚ) ^ M /
          (2 * (Y : ℚ) - (h : ℚ)) ≤
        (3 / 2 : ℚ) * ((H : ℚ) * (2 : ℚ) ^ M / (Y : ℚ)) := by
    calc
      2 * (h : ℚ) * (2 : ℚ) ^ M /
          (2 * (Y : ℚ) - (h : ℚ)) ≤
          (3 / 2 : ℚ) * (H : ℚ) * (2 : ℚ) ^ M / (Y : ℚ) := hterm
      _ = (3 / 2 : ℚ) * ((H : ℚ) * (2 : ℚ) ^ M / (Y : ℚ)) := by ring
  have hfinal :
      ((taggedFiber M Y h y).card : ℚ) ≤
        (5 / 2 : ℚ) * ((H : ℚ) * (2 : ℚ) ^ M / (Y : ℚ)) := by
    nlinarith
  convert hfinal using 1
  ring
end FirstPassageLinearTransport
