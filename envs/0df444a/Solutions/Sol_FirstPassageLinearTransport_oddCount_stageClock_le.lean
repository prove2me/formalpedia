-- Prove2me | solution 1 for FirstPassageLinearTransport.oddCount_stageClock_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:45.970708+00:00
-- url     : https://prove2.me/submissions/4c0544d2-faa7-484d-84f0-cad85a1066c7

import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_ClockBudget
import Definitions.Def_FirstPassageLinearTransport_RawClockBudget
import Theorems.Thm_FirstPassageLinearTransport_oddCount_upper_of_initialWindowGood
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_succ
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_clockGeom_le_nat
import Theorems.Thm_FirstPassageLinearTransport_clockGeom_nonneg
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_initialWindowGood_of_mem_extended_of_large
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_add
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_pos
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_succ
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageK_one_le
import Theorems.Thm_FirstPassageLinearTransport_stageK_pos
import Theorems.Thm_FirstPassageLinearTransport_stageLength_le_log
import Theorems.Thm_FirstPassageLinearTransport_stageMap_is_actual
import Theorems.Thm_FirstPassageLinearTransport_stageMap_le_power
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r eta : ℝ} (p : StageSetup r eta) {R n : ℕ}
    (hn : 0 < n) (hnSet : n ∈ bootstrapSet p R) :
    (oddCount n (stageClock p R n) : ℝ) ≤
      (stageClock p R n : ℝ) / 2 +
        eta / Real.log 3 *
          (clockGeom r R * Real.log n +
            (R : ℝ) ^ 2 * Real.log (stageK p)) := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  induction R generalizing n with
  | zero => simp [clockGeom]
  | succ R ih =>
      rw [bootstrapSet_succ] at hnSet
      have hnW := hnSet.1
      have hchildSet := hnSet.2
      have hchildPos : 0 < stageMap p n := by
        rw [stageMap_is_actual]
        exact orbit_pos hn _
      have hlenNat := stageLength_le_log p hn hnW
      have hblock :
          (oddCount n (stageLength p n) : ℝ) ≤
            (stageLength p n : ℝ) / 2 +
              eta * Real.log n / Real.log 3 := by
        by_cases hlarge : p.M0 ≤ Nat.log 2 n
        · have hgood := mem_initialWindowGood_of_mem_extended_of_large
            p hnW hlarge
          exact oddCount_upper_of_initialWindowGood hn hgood hlenNat
        · have hlen0 : stageLength p n = 0 := by
            simp [stageLength, hlarge]
          rw [hlen0]
          simp only [oddCount_zero, Nat.cast_zero, zero_div, zero_add]
          have hn1R : (1 : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast (show 1 ≤ n by omega)
          exact div_nonneg
            (mul_nonneg p.eta_pos.le
              (Real.log_nonneg hn1R))
            hlog3.le
      have hIH := ih hchildPos hchildSet
      have hclockAdd : stageClock p (R + 1) n =
          stageLength p n + stageClock p R (stageMap p n) :=
        stageClock_succ p R n
      have hoddAdd :
          oddCount n (stageClock p (R + 1) n) =
            oddCount n (stageLength p n) +
              oddCount (stageMap p n) (stageClock p R (stageMap p n)) := by
        rw [hclockAdd, oddCount_add, stageMap_is_actual]
      have hlogMap : Real.log (stageMap p n) ≤
          Real.log (stageK p) + r * Real.log n := by
        have hstage := stageMap_le_power p hn hnW
        have hmono := Real.log_le_log (by exact_mod_cast hchildPos)
          hstage
        calc
          Real.log (stageMap p n) ≤
              Real.log (stageK p * (n : ℝ) ^ r) := hmono
          _ = Real.log (stageK p) + r * Real.log n := by
            rw [Real.log_mul (stageK_pos p).ne'
              (Real.rpow_pos_of_pos (by exact_mod_cast hn) r).ne',
              Real.log_rpow (by exact_mod_cast hn)]
      rw [hoddAdd, hclockAdd]
      push_cast
      have hgeom0 := clockGeom_nonneg p.r_pos.le R
      have hgeomR := clockGeom_le_nat p.r_pos.le p.r_lt_one.le R
      have heta0 := p.eta_pos.le
      have hlogK0 : 0 ≤ Real.log (stageK p) :=
        Real.log_nonneg (stageK_one_le p)
      rw [clockGeom]
      have hweightedLog := mul_le_mul_of_nonneg_left hlogMap hgeom0
      have hn1R : (1 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (show 1 ≤ n by omega)
      have hprofile :
          Real.log n +
              (clockGeom r R * Real.log (stageMap p n) +
                (R : ℝ) ^ 2 * Real.log (stageK p)) ≤
            (1 + r * clockGeom r R) * Real.log n +
              ((R : ℝ) + 1) ^ 2 * Real.log (stageK p) := by
        have hgeomLogK := mul_le_mul_of_nonneg_right hgeomR hlogK0
        calc
          Real.log n +
                (clockGeom r R * Real.log (stageMap p n) +
                  (R : ℝ) ^ 2 * Real.log (stageK p)) ≤
              Real.log n +
                (clockGeom r R *
                    (Real.log (stageK p) + r * Real.log n) +
                  (R : ℝ) ^ 2 * Real.log (stageK p)) := by
            linarith
          _ ≤ (1 + r * clockGeom r R) * Real.log n +
                ((R : ℝ) + 1) ^ 2 * Real.log (stageK p) := by
            nlinarith
      have hq0 : 0 ≤ eta / Real.log 3 := div_nonneg heta0 hlog3.le
      have hweightedProfile := mul_le_mul_of_nonneg_left hprofile hq0
      have hblock' :
          (oddCount n (stageLength p n) : ℝ) ≤
            (stageLength p n : ℝ) / 2 +
              eta / Real.log 3 * Real.log n := by
        convert hblock using 1
        ring
      nlinarith
end FirstPassageLinearTransport
