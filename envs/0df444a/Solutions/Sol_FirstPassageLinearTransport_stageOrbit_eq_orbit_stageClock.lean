-- Prove2me | solution 1 for FirstPassageLinearTransport.stageOrbit_eq_orbit_stageClock
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:35:37.321797+00:00
-- url     : https://prove2.me/submissions/0863ffa7-ba9c-451e-b221-fb38febc1a24

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_succ
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_succ
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_add
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
theorem _root_.solution {r eta : ℝ}
    (p : StageSetup r eta) (R n : ℕ) :
    stageOrbit p R n = orbit (stageClock p R n) n := by
  induction R generalizing n with
  | zero => simp
  | succ R ih =>
      rw [stageOrbit_succ, ih, stageClock_succ, add_comm,
        orbit_add, ← stageMap_is_actual]
end FirstPassageLinearTransport
