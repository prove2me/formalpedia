-- Prove2me | solution 1 for FirstPassageLinearTransport.bootstrapSet_powerDense
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:57:54.995544+00:00
-- url     : https://prove2.me/submissions/88b1b78d-7483-4bea-a51c-49d8fa46d1d3

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_succ
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_succ
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_succ
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_le_Dc
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_degrade_exponent
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_extendedWindow_powerDense
import Theorems.Thm_FirstPassageLinearTransport_firstPassagePullback_powerDense
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
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
theorem _root_.solution
    {r eta chi Dc : ℝ} (p : StageSetup r eta)
    (hchi0 : 0 < chi) (hchir : chi < r) (hchi1 : chi ≤ 1)
    (hDc0 : 0 < Dc)
    (hDcRate : Dc ≤ quadraticWindowDensityRate eta)
    (hchiDc : chi * Dc < 1) :
    ∀ R, PowerDense (bootstrapSet p R)
      (bootstrapC p chi Dc R) (bootstrapD chi Dc R) := by
  intro R
  induction R with
  | zero =>
      simpa using (extendedWindow_powerDense p).degrade_exponent hDc0 hDcRate
  | succ R ih =>
      rw [bootstrapSet_succ, bootstrapC_succ, bootstrapD_succ]
      apply firstPassagePullback_powerDense p (bootstrapSet p R) ih
        hchi0 hchir hDc0
      · exact bootstrapD_le_Dc hchi0.le hchi1 hDc0.le R
      · have hmul : chi * Dc ≤ 1 * Dc :=
          mul_le_mul_of_nonneg_right hchi1 hDc0.le
        have hmul' : chi * Dc ≤ Dc := by simpa only [one_mul] using hmul
        exact hmul'.trans hDcRate
      · exact hchiDc
end FirstPassageLinearTransport
