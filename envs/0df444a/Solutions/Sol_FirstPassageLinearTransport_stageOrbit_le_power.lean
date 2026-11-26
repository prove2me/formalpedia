-- Prove2me | solution 1 for FirstPassageLinearTransport.stageOrbit_le_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:57:20.029606+00:00
-- url     : https://prove2.me/submissions/7391fb0e-3364-40b3-8a21-f33563f1e185

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_succ
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_stageK_pos
import Theorems.Thm_FirstPassageLinearTransport_stageK_one_le
import Theorems.Thm_FirstPassageLinearTransport_stageMap_le_power
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_succ
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
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
    (stageOrbit p R n : ℝ) ≤
      stageK p ^ R * (n : ℝ) ^ (r ^ R) := by
  induction R generalizing n with
  | zero => simp
  | succ R ih =>
      rw [bootstrapSet_succ] at hnSet
      have hnW : n ∈ extendedWindow p := hnSet.1
      have hmapSet : stageMap p n ∈ bootstrapSet p R := hnSet.2
      have hmapPos : 0 < stageMap p n := by
        rw [stageMap_is_actual]
        exact orbit_pos hn _
      have hIH := ih hmapPos hmapSet
      have hstage := stageMap_le_power p hn hnW
      have hr0 : 0 ≤ r := p.r_pos.le
      have hr1 : r ≤ 1 := p.r_lt_one.le
      have hrPow0 : 0 ≤ r ^ R := pow_nonneg hr0 _
      have hrPow1 : r ^ R ≤ 1 := pow_le_one₀ hr0 hr1
      have hraise :
          (stageMap p n : ℝ) ^ (r ^ R) ≤
            (stageK p * (n : ℝ) ^ r) ^ (r ^ R) :=
        Real.rpow_le_rpow (by positivity) hstage hrPow0
      have hKpow : stageK p ^ (r ^ R) ≤ stageK p := by
        have hlog := Real.rpow_le_rpow_of_exponent_le
          (stageK_one_le p) hrPow1
        simpa [Real.rpow_one] using hlog
      rw [stageOrbit_succ]
      calc
        (stageOrbit p R (stageMap p n) : ℝ) ≤
            stageK p ^ R * (stageMap p n : ℝ) ^ (r ^ R) := hIH
        _ ≤ stageK p ^ R *
            (stageK p * (n : ℝ) ^ r) ^ (r ^ R) :=
          mul_le_mul_of_nonneg_left hraise
            (pow_nonneg (stageK_pos p).le R)
        _ = stageK p ^ R *
            (stageK p ^ (r ^ R) *
              ((n : ℝ) ^ r) ^ (r ^ R)) := by
          rw [Real.mul_rpow (stageK_pos p).le (by positivity)]
        _ ≤ stageK p ^ R *
            (stageK p * ((n : ℝ) ^ r) ^ (r ^ R)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hKpow (by positivity))
            (pow_nonneg (stageK_pos p).le R)
        _ = stageK p ^ (R + 1) * (n : ℝ) ^ (r ^ (R + 1)) := by
          rw [pow_succ, pow_succ, ← Real.rpow_mul (by positivity)]
          ring
end FirstPassageLinearTransport
