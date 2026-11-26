-- Prove2me | solution 1 for FirstPassageLinearTransport.stageMap_le_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:20:04.442181+00:00
-- url     : https://prove2.me/submissions/0b30dfac-772d-48f9-8887-bd182834adf8

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell_log
import Theorems.Thm_FirstPassageLinearTransport_stageK_pos
import Theorems.Thm_FirstPassageLinearTransport_stageK_one_le
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_initialWindowGood_of_mem_extended_of_large
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageLength_isFirstPassage
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero


attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {r eta : ℝ} (p : StageSetup r eta)
    {n : ℕ} (hn : 0 < n) (hnW : n ∈ extendedWindow p) :
    (stageMap p n : ℝ) ≤ stageK p * (n : ℝ) ^ r := by
  let M := Nat.log 2 n
  have hshell : n ∈ dyadicShell M := mem_dyadicShell_log hn
  by_cases hlarge : p.M0 ≤ M
  · have hgood := mem_initialWindowGood_of_mem_extended_of_large p hnW hlarge
    have hfp := stageLength_isFirstPassage p hlarge hshell hgood
    have hstage : (stageMap p n : ℝ) ≤ targetScale r M := by
      exact_mod_cast hfp.1
    have hrM0 : 0 ≤ r * (M : ℝ) :=
      mul_nonneg p.r_pos.le (Nat.cast_nonneg M)
    have hfloor : (⌊r * (M : ℝ)⌋₊ : ℝ) ≤ r * M :=
      Nat.floor_le hrM0
    have htarget : (targetScale r M : ℝ) ≤ (2 : ℝ) ^ (r * M) := by
      unfold targetScale
      rw [Nat.cast_pow, ← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hfloor
    have hbase : (2 : ℝ) ^ M ≤ n := by
      exact_mod_cast (mem_dyadicShell.mp hshell).1
    have hpow : (2 : ℝ) ^ (r * M) ≤ (n : ℝ) ^ r := by
      calc
        (2 : ℝ) ^ (r * M) = (2 : ℝ) ^ ((M : ℝ) * r) := by ring_nf
        _ = ((2 : ℝ) ^ M) ^ r := by
          rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
        _ ≤ (n : ℝ) ^ r :=
          Real.rpow_le_rpow (by positivity) hbase p.r_pos.le
    have hKmul : (n : ℝ) ^ r ≤ stageK p * (n : ℝ) ^ r := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (stageK_one_le p)
          (Real.rpow_nonneg (by positivity) r)
    exact hstage.trans (htarget.trans (hpow.trans hKmul))
  · have hstage : stageMap p n = n := by
      simp [stageMap, stageLength, M, hlarge]
    have hnK : (n : ℝ) ≤ stageK p := by
      have hnlt : n < 2 ^ p.M0 := by
        have hnlog : Nat.log 2 n < p.M0 := by omega
        exact (mem_dyadicShell.mp hshell).2.trans_le
          (Nat.pow_le_pow_right (by norm_num) (by omega))
      unfold stageK
      exact_mod_cast hnlt.le
    have hpow1 : 1 ≤ (n : ℝ) ^ r := by
      exact Real.one_le_rpow (by exact_mod_cast hn) p.r_pos.le
    rw [hstage]
    calc
      (n : ℝ) ≤ stageK p := hnK
      _ = stageK p * 1 := by ring
      _ ≤ stageK p * (n : ℝ) ^ r :=
        mul_le_mul_of_nonneg_left hpow1 (stageK_pos p).le
end FirstPassageLinearTransport
