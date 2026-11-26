-- Prove2me | solution 1 for FirstPassageLinearTransport.firstPassagePullback_powerDense
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:44:19.519887+00:00
-- url     : https://prove2.me/submissions/e53638c0-94c1-42b2-8e2d-2d60b028542f

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Theorems.Thm_FirstPassageLinearTransport_pullbackShellConstant_pos
import Theorems.Thm_FirstPassageLinearTransport_firstPassagePullback_shell_bound
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_C_pos
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_le_one
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_pos
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_mono_constant
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_powerDense_of_shell_bound
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
    {r eta C D chi Dc : ℝ} (p : StageSetup r eta)
    (S : Set ℕ) (hS : PowerDense S C D)
    (hchi0 : 0 < chi) (hchi : chi < r)
    (hDc0 : 0 < Dc)
    (hDDc : D ≤ Dc)
    (hDcRate : chi * Dc ≤ quadraticWindowDensityRate eta)
    (hchiDc : chi * Dc < 1) :
    PowerDense (firstPassagePullback p S)
      (pullbackGlobalConstant p chi Dc * (C + 1) * D⁻¹ ^ 2)
      (chi * D) := by
  have hD0 := hS.D_pos
  have hD1 := hS.D_le_one
  have hc0 : 0 < chi * D * Real.log 2 := by positivity
  have hcLt : chi * D * Real.log 2 < Real.log 2 := by
    have : chi * D < 1 :=
      (mul_le_mul_of_nonneg_left hDDc hchi0.le).trans_lt hchiDc
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hK0 :
      0 < pullbackShellConstant p chi Dc * (C + 1) * D⁻¹ ^ 2 := by
    exact mul_pos
      (mul_pos (pullbackShellConstant_pos p hchi) (by linarith [hS.C_pos]))
      (sq_pos_of_pos (inv_pos.mpr hD0))
  have hshell : ∀ M : ℕ,
      ((shellBad (firstPassagePullback p S) M).card : ℝ) ≤
        (pullbackShellConstant p chi Dc * (C + 1) * D⁻¹ ^ 2) *
          Real.exp (-(chi * D * Real.log 2) * M) * (2 : ℝ) ^ M := by
    intro M
    convert firstPassagePullback_shell_bound p S hS hchi0 hchi hDc0
      hDDc hDcRate M using 1
    all_goals ring
  have hraw := powerDense_of_shell_bound hK0 hc0 hcLt hshell
  have hlog2ne : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  have hrateEq : chi * D * Real.log 2 / Real.log 2 = chi * D := by
    field_simp [hlog2ne]
  rw [hrateEq] at hraw
  have hdenDc : 0 < 2 * Real.exp (-(chi * Dc * Real.log 2)) - 1 := by
    have hExpLog : Real.exp (-Real.log 2) = (1 : ℝ) / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
    have hlt : -Real.log 2 < -(chi * Dc * Real.log 2) := by
      have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      nlinarith
    have hexp := Real.exp_lt_exp.2 hlt
    rw [hExpLog] at hexp
    linarith
  have hden :
      2 * Real.exp (-(chi * Dc * Real.log 2)) - 1 ≤
        2 * Real.exp (-(chi * D * Real.log 2)) - 1 := by
    have hrate := mul_le_mul_of_nonneg_left hDDc hchi0.le
    have hexp :
        Real.exp (-(chi * Dc * Real.log 2)) ≤
          Real.exp (-(chi * D * Real.log 2)) := by
      apply Real.exp_le_exp.2
      have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      nlinarith
    nlinarith
  apply hraw.mono_constant
  unfold pullbackGlobalConstant
  have hnum :
      0 ≤ 2 * pullbackShellConstant p chi Dc * (C + 1) * D⁻¹ ^ 2 := by
    exact (mul_pos
      (mul_pos (mul_pos (by norm_num) (pullbackShellConstant_pos p hchi))
        (by linarith [hS.C_pos]))
      (sq_pos_of_pos (inv_pos.mpr hD0))).le
  have hdiv := div_le_div_of_nonneg_left hnum hdenDc hden
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
end FirstPassageLinearTransport
