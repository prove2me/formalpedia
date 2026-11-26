-- Prove2me | solution 1 for FirstPassageLinearTransport.certified_firstPassage_duration_corridor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:38:26.99269+00:00
-- url     : https://prove2.me/submissions/4461d010-d3c8-4776-9525-1e2e76edc07a

import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierCore
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_centralOrbitScale_eq_two_rpow_neg_gap
import Theorems.Thm_FirstPassageLinearTransport_centralOrbitScale_pos
import Theorems.Thm_FirstPassageLinearTransport_firstPassage_band
import Theorems.Thm_FirstPassageLinearTransport_log_two_eq_of_mem_dyadicShell
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
    {x m q h : ℕ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hxShell : x ∈ dyadicShell m)
    (hxGood : x ∈ initialWindowGood t)
    (hhm : h ≤ m) (hh : 0 < h)
    (hfp : IsFirstPassage (2 ^ q) x h) :
    (1 - t) * (m : ℝ) - (q : ℝ) ≤ driftGap * (h : ℝ) ∧
      driftGap * (h : ℝ) <
        (1 + t) * ((m : ℝ) + 1) - (q : ℝ) + 1 := by
  have hlog := log_two_eq_of_mem_dyadicShell hxShell
  have henv := hxGood h (by simpa [hlog] using hhm)
  have hband := firstPassage_band hh hfp
  have hxLowerNat := (mem_dyadicShell.mp hxShell).1
  have hxUpperNat := (mem_dyadicShell.mp hxShell).2
  have hxLower : (2 : ℝ) ^ m ≤ (x : ℝ) := by exact_mod_cast hxLowerNat
  have hxUpper : (x : ℝ) ≤ (2 : ℝ) ^ (m + 1) := by
    exact_mod_cast hxUpperNat.le
  have hexpLower : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hexpUpper : 0 ≤ 1 + t := by linarith
  have hsourceLower :
      ((2 : ℝ) ^ m) ^ (1 - t) ≤ (x : ℝ) ^ (1 - t) :=
    Real.rpow_le_rpow (by positivity) hxLower hexpLower
  have hsourceUpper :
      (x : ℝ) ^ (1 + t) ≤ ((2 : ℝ) ^ (m + 1)) ^ (1 + t) :=
    Real.rpow_le_rpow (by positivity) hxUpper hexpUpper
  have hlandingUpper : (orbit h x : ℝ) ≤ (2 : ℝ) ^ q := by
    exact_mod_cast hfp.1
  have hlandingLower : (2 : ℝ) ^ ((q : ℝ) - 1) < (orbit h x : ℝ) := by
    have hcast : (2 : ℝ) ^ q < 2 * (orbit h x : ℝ) := by
      exact_mod_cast hband.1
    have hcast' : (2 : ℝ) ^ (q : ℝ) < 2 * (orbit h x : ℝ) := by
      simpa [Real.rpow_natCast] using hcast
    rw [Real.rpow_sub (by norm_num), Real.rpow_one]
    nlinarith [hcast']
  have hpowLower :
      (2 : ℝ) ^ (-driftGap * (h : ℝ) + (m : ℝ) * (1 - t)) ≤
        (2 : ℝ) ^ (q : ℝ) := by
    calc
      (2 : ℝ) ^ (-driftGap * (h : ℝ) + (m : ℝ) * (1 - t)) =
          centralOrbitScale h * (((2 : ℝ) ^ m) ^ (1 - t)) := by
        rw [centralOrbitScale_eq_two_rpow_neg_gap,
          ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
      _ ≤ centralOrbitScale h * (x : ℝ) ^ (1 - t) :=
        mul_le_mul_of_nonneg_left hsourceLower (centralOrbitScale_pos h).le
      _ ≤ (orbit h x : ℝ) := henv.1
      _ ≤ (2 : ℝ) ^ q := hlandingUpper
      _ = (2 : ℝ) ^ (q : ℝ) := by rw [Real.rpow_natCast]
  have hpowUpper :
      (2 : ℝ) ^ ((q : ℝ) - 1) <
        (2 : ℝ) ^ (-driftGap * (h : ℝ) +
          ((m : ℝ) + 1) * (1 + t)) := by
    calc
      (2 : ℝ) ^ (q - 1 : ℝ) < (orbit h x : ℝ) := hlandingLower
      _ ≤ centralOrbitScale h * (x : ℝ) ^ (1 + t) := henv.2
      _ ≤ centralOrbitScale h * (((2 : ℝ) ^ (m + 1)) ^ (1 + t)) :=
        mul_le_mul_of_nonneg_left hsourceUpper (centralOrbitScale_pos h).le
      _ = (2 : ℝ) ^ (-driftGap * (h : ℝ) +
          ((m : ℝ) + 1) * (1 + t)) := by
        rw [centralOrbitScale_eq_two_rpow_neg_gap,
          ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
        congr 1
        norm_num
  have hmono := Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)
  have hlowerExp :
      -driftGap * (h : ℝ) + (m : ℝ) * (1 - t) ≤ (q : ℝ) :=
    hmono.le_iff_le.mp hpowLower
  have hupperExp :
      (q : ℝ) - 1 < -driftGap * (h : ℝ) +
        ((m : ℝ) + 1) * (1 + t) :=
    hmono.lt_iff_lt.mp hpowUpper
  constructor <;> nlinarith
end FirstPassageLinearTransport
