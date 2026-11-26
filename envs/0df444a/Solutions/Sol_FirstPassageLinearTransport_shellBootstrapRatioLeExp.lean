-- Prove2me | solution 1 for FirstPassageLinearTransport.shellBootstrapRatioLeExp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:00:31.738941+00:00
-- url     : https://prove2.me/submissions/0a67223a-4416-457d-b25b-736fc185560a

import Definitions.Def_FirstPassageLinearTransport_GlobalAssembly
import Definitions.Def_FirstPassageLinearTransport_BootstrapSchedule
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_exp_bound
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_pos
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_powerDense
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shellExceptionalRatio_le_of_powerDense
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
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
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
open Filter
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r eta chi Dc : ℝ} (p : StageSetup r eta)
    (hchi0 : 0 < chi) (hchir : chi < r) (hchi1 : chi ≤ 1)
    (hDc0 : 0 < Dc) (hDc1 : Dc ≤ 1)
    (hDcRate : Dc ≤ quadraticWindowDensityRate eta)
    (hchiDc : chi * Dc < 1) (R M : ℕ) :
    shellExceptionalRatio (bootstrapSet p R) M ≤
      Real.exp (Real.log 2 + bootstrapLogBound p chi Dc R -
        Real.log 2 * bootstrapD chi Dc R * M) := by
  have hPD := bootstrapSet_powerDense p hchi0 hchir hchi1
    hDc0 hDcRate hchiDc R
  have hshell := shellExceptionalRatio_le_of_powerDense hPD M
  have hC := bootstrapC_exp_bound p hchi0 hchir hchi1
    hDc0 hDc1 hchiDc R
  have hCpos := (bootstrapC_pos p hchi0 hchir hDc0 hchiDc R).le
  have hlog2 : Real.exp (Real.log 2) = 2 :=
    Real.exp_log (by norm_num)
  calc
    shellExceptionalRatio (bootstrapSet p R) M
        ≤ 2 * bootstrapC p chi Dc R *
            Real.exp (-(Real.log 2 * bootstrapD chi Dc R * M)) := hshell
    _ ≤ 2 * (bootstrapC p chi Dc R + 2) *
            Real.exp (-(Real.log 2 * bootstrapD chi Dc R * M)) := by
          gcongr
          · linarith
    _ ≤ 2 * Real.exp (bootstrapLogBound p chi Dc R) *
            Real.exp (-(Real.log 2 * bootstrapD chi Dc R * M)) := by
          gcongr
          simpa [bootstrapLogBound] using hC
    _ = Real.exp (Real.log 2 + bootstrapLogBound p chi Dc R -
          Real.log 2 * bootstrapD chi Dc R * M) := by
          rw [show Real.log 2 + bootstrapLogBound p chi Dc R -
              Real.log 2 * bootstrapD chi Dc R * M =
            Real.log 2 + (bootstrapLogBound p chi Dc R -
              Real.log 2 * bootstrapD chi Dc R * M) by ring,
            Real.exp_add, hlog2]
          rw [mul_assoc, ← Real.exp_add]
          congr 1
end FirstPassageLinearTransport
