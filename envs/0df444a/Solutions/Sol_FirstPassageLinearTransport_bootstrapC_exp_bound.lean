-- Prove2me | solution 1 for FirstPassageLinearTransport.bootstrapC_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:59:08.515031+00:00
-- url     : https://prove2.me/submissions/ee6be14d-5ed1-4c27-81d6-a86c565f3057

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_pos
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_terminal_bound
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_C_pos
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_extendedWindow_powerDense
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_pullbackShellConstant_pos
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
    {r eta chi Dc : ℝ} (p : StageSetup r eta)
    (hchi0 : 0 < chi) (hchir : chi < r) (hchi1 : chi ≤ 1)
    (hDc0 : 0 < Dc) (hDc1 : Dc ≤ 1) (hchiDc : chi * Dc < 1)
    (R : ℕ) :
    bootstrapC p chi Dc R + 2 ≤ Real.exp
      (Real.log (quadraticWindowGlobalConstant eta + 2) +
        (R : ℝ) * Real.log (bootstrapStageK p chi Dc) +
        2 * (R : ℝ) * Real.log Dc⁻¹ +
        2 * (R : ℝ) ^ 2 * Real.log chi⁻¹) := by
  have hterm := bootstrapC_terminal_bound p hchi0 hchir hchi1
    hDc0 hDc1 hchiDc R
  let B := quadraticWindowGlobalConstant eta + 2
  let S := bootstrapStageK p chi Dc
  let D := bootstrapD chi Dc R
  have hB : 0 < B := by dsimp [B]; linarith [(extendedWindow_powerDense p).C_pos]
  have hS : 0 < S := by
    dsimp [S, bootstrapStageK]
    have hnum : 0 < 2 * pullbackShellConstant p chi Dc :=
      mul_pos (by norm_num) (pullbackShellConstant_pos p hchir)
    have hden : 0 < 2 * Real.exp (-(chi * Dc * Real.log 2)) - 1 := by
      have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      have hlt : -Real.log 2 < -(chi * Dc * Real.log 2) := by nlinarith
      have hexp := Real.exp_lt_exp.2 hlt
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hexp
      nlinarith
    have hK : 0 < pullbackGlobalConstant p chi Dc := by
      simpa [pullbackGlobalConstant] using div_pos hnum hden
    linarith
  have hD : 0 < D := by dsimp [D]; exact bootstrapD_pos hchi0 hDc0 R
  have hRHS : 0 < B * (S * D⁻¹ ^ 2) ^ R := by positivity
  have hlog : Real.log (B * (S * D⁻¹ ^ 2) ^ R) =
      Real.log B + (R : ℝ) * Real.log S +
        2 * (R : ℝ) * Real.log Dc⁻¹ +
        2 * (R : ℝ) ^ 2 * Real.log chi⁻¹ := by
    have hDcne := hDc0.ne'
    have hchine := hchi0.ne'
    have hDform : D⁻¹ = Dc⁻¹ * (chi⁻¹) ^ R := by
      dsimp [D, bootstrapD]
      rw [mul_inv, inv_pow]
    rw [Real.log_mul hB.ne' (pow_ne_zero R (mul_ne_zero hS.ne'
        (pow_ne_zero 2 (inv_ne_zero hD.ne')))),
      Real.log_pow, Real.log_mul hS.ne' (pow_ne_zero 2 (inv_ne_zero hD.ne')),
      Real.log_pow, hDform,
      Real.log_mul (inv_ne_zero hDcne) (pow_ne_zero R (inv_ne_zero hchine)),
      Real.log_pow]
    push_cast
    ring
  apply hterm.trans
  apply (Real.log_le_iff_le_exp hRHS).1
  rw [hlog]
end FirstPassageLinearTransport
