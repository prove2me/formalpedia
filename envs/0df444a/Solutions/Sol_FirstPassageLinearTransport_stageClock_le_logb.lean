-- Prove2me | solution 1 for FirstPassageLinearTransport.stageClock_le_logb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:36:06.119816+00:00
-- url     : https://prove2.me/submissions/ba1aea04-ae9e-4081-a662-f1b5db86a20d

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_succ
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_stageLength_le_log
import Theorems.Thm_FirstPassageLinearTransport_stageK_pos
import Theorems.Thm_FirstPassageLinearTransport_stageK_one_le
import Theorems.Thm_FirstPassageLinearTransport_stageMap_le_power
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_succ
import Theorems.Thm_FirstPassageLinearTransport_clockGeom_nonneg
import Theorems.Thm_FirstPassageLinearTransport_clockGeom_le_nat
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_pos
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageMap_is_actual
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
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.stageClock_zero

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r eta : ℝ} (p : StageSetup r eta) {R n : ℕ}
    (hn : 0 < n) (hnSet : n ∈ bootstrapSet p R) :
    (stageClock p R n : ℝ) ≤
      clockGeom r R * Real.logb 2 n +
        (R : ℝ) ^ 2 * Real.logb 2 (stageK p) := by
  induction R generalizing n with
  | zero => simp [clockGeom]
  | succ R ih =>
      rw [bootstrapSet_succ] at hnSet
      have hnW := hnSet.1
      have hmapSet := hnSet.2
      have hmapPos : 0 < stageMap p n := by
        rw [stageMap_is_actual]
        exact orbit_pos hn _
      have hlenNat := stageLength_le_log p hn hnW
      have hlenCast : (stageLength p n : ℝ) ≤ (Nat.log 2 n : ℝ) := by
        exact_mod_cast hlenNat
      have hlen : (stageLength p n : ℝ) ≤ Real.logb 2 n :=
        hlenCast.trans (Real.natLog_le_logb n 2)
      have hIH := ih hmapPos hmapSet
      have hstage := stageMap_le_power p hn hnW
      have hlogMap : Real.logb 2 (stageMap p n) ≤
          Real.logb 2 (stageK p) + r * Real.logb 2 n := by
        have hmono := (Real.logb_le_logb (b := (2 : ℝ)) (by norm_num)
          (by exact_mod_cast hmapPos) (mul_pos (stageK_pos p)
            (Real.rpow_pos_of_pos (by exact_mod_cast hn) r))).2 hstage
        calc
          Real.logb 2 (stageMap p n) ≤
              Real.logb 2 (stageK p * (n : ℝ) ^ r) := hmono
          _ = Real.logb 2 (stageK p) + Real.logb 2 ((n : ℝ) ^ r) := by
            rw [Real.logb_mul (stageK_pos p).ne'
              (Real.rpow_pos_of_pos (by exact_mod_cast hn) r).ne']
          _ = Real.logb 2 (stageK p) + r * Real.logb 2 n := by
            rw [Real.logb_rpow_eq_mul_logb_of_pos (by exact_mod_cast hn)]
      have hgeom0 := clockGeom_nonneg p.r_pos.le R
      have hlogK0 : 0 ≤ Real.logb 2 (stageK p) :=
        Real.logb_nonneg (by norm_num) (stageK_one_le p)
      have hmain :
          (stageLength p n : ℝ) + (stageClock p R (stageMap p n) : ℝ) ≤
            clockGeom r (R + 1) * Real.logb 2 n +
              ((R : ℝ) + 1) ^ 2 * Real.logb 2 (stageK p) := by
        calc
        (stageLength p n : ℝ) + (stageClock p R (stageMap p n) : ℝ)
            ≤ Real.logb 2 n +
              (clockGeom r R * Real.logb 2 (stageMap p n) +
                (R : ℝ) ^ 2 * Real.logb 2 (stageK p)) :=
          add_le_add hlen hIH
        _ ≤ Real.logb 2 n +
              (clockGeom r R *
                  (Real.logb 2 (stageK p) + r * Real.logb 2 n) +
                (R : ℝ) ^ 2 * Real.logb 2 (stageK p)) := by
          gcongr
        _ ≤ clockGeom r (R + 1) * Real.logb 2 n +
              ((R : ℝ) + 1) ^ 2 * Real.logb 2 (stageK p) := by
          rw [clockGeom]
          have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
          have hpay : clockGeom r R ≤ 2 * R + 1 :=
            (clockGeom_le_nat p.r_pos.le p.r_lt_one.le R).trans (by linarith)
          nlinarith
      rw [stageClock_succ]
      push_cast
      simpa only [Nat.cast_add, Nat.cast_one] using hmain
end FirstPassageLinearTransport
