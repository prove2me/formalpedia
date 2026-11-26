-- Prove2me | solution 1 for FirstPassageLinearTransport.bootstrapC_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:34:36.567131+00:00
-- url     : https://prove2.me/submissions/f9977c0e-afb9-4332-b561-c17cf938d713

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_succ
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_pos
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

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {r eta chi Dc : ℝ} (p : StageSetup r eta)
    (hchi0 : 0 < chi) (hchir : chi < r)
    (hDc0 : 0 < Dc) (hchiDc : chi * Dc < 1) :
    ∀ R, 0 < bootstrapC p chi Dc R := by
  intro R
  induction R with
  | zero =>
      simpa using (extendedWindow_powerDense p).C_pos
  | succ R ih =>
      rw [bootstrapC_succ]
      have hK : 0 < pullbackGlobalConstant p chi Dc := by
        have hnum : 0 < 2 * pullbackShellConstant p chi Dc := by
          exact mul_pos (by norm_num) (pullbackShellConstant_pos p hchir)
        have hden : 0 < 2 * Real.exp (-(chi * Dc * Real.log 2)) - 1 := by
          have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
          have hlt : -Real.log 2 < -(chi * Dc * Real.log 2) := by
            nlinarith
          have hexp := Real.exp_lt_exp.2 hlt
          rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hexp
          nlinarith
        simpa [pullbackGlobalConstant] using div_pos hnum hden
      have hD := bootstrapD_pos hchi0 hDc0 R
      positivity
end FirstPassageLinearTransport
