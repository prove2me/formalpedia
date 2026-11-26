-- Prove2me | solution 1 for FirstPassageLinearTransport.collatz_support_unique_in_unit_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:03.733961+00:00
-- url     : https://prove2.me/submissions/a8a08cf7-f839-4eee-9f53-193720727bc8

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_one_lt_log_three
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
    {k l : ℕ} {a : ℝ}
    (hklo : a ≤ (k : ℝ) * Real.log 3)
    (hkhi : (k : ℝ) * Real.log 3 < a + 1)
    (hllo : a ≤ (l : ℝ) * Real.log 3)
    (hlhi : (l : ℝ) * Real.log 3 < a + 1) :
    k = l := by
  rcases lt_trichotomy k l with hkl | hkl | hkl
  · have hcast : (1 : ℝ) ≤ (l : ℝ) - (k : ℝ) := by
      have hc : ((k + 1 : ℕ) : ℝ) ≤ (l : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hkl)
      norm_num at hc ⊢
      linarith
    have hmul : Real.log 3 ≤ ((l : ℝ) - (k : ℝ)) * Real.log 3 := by
      simpa using mul_le_mul_of_nonneg_right hcast
        (zero_le_one.trans one_lt_log_three.le)
    have hgap :
        (1 : ℝ) < (l : ℝ) * Real.log 3 - (k : ℝ) * Real.log 3 := by
      calc
        (1 : ℝ) < Real.log 3 := one_lt_log_three
        _ ≤ ((l : ℝ) - (k : ℝ)) * Real.log 3 := hmul
        _ = (l : ℝ) * Real.log 3 - (k : ℝ) * Real.log 3 := by ring
    linarith
  · exact hkl
  · have hcast : (1 : ℝ) ≤ (k : ℝ) - (l : ℝ) := by
      have hc : ((l + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hkl)
      norm_num at hc ⊢
      linarith
    have hmul : Real.log 3 ≤ ((k : ℝ) - (l : ℝ)) * Real.log 3 := by
      simpa using mul_le_mul_of_nonneg_right hcast
        (zero_le_one.trans one_lt_log_three.le)
    have hgap :
        (1 : ℝ) < (k : ℝ) * Real.log 3 - (l : ℝ) * Real.log 3 := by
      calc
        (1 : ℝ) < Real.log 3 := one_lt_log_three
        _ ≤ ((k : ℝ) - (l : ℝ)) * Real.log 3 := hmul
        _ = (k : ℝ) * Real.log 3 - (l : ℝ) * Real.log 3 := by ring
    linarith
end FirstPassageLinearTransport
