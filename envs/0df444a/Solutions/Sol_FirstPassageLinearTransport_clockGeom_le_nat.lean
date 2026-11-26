-- Prove2me | solution 1 for FirstPassageLinearTransport.clockGeom_le_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:35:07.137674+00:00
-- url     : https://prove2.me/submissions/5a14c739-8e8b-4bb2-b647-10a23202a472

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_clockGeom_nonneg
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
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
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.stageClock_zero

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∀ R, clockGeom r R ≤ R := by
  intro R
  induction R with
  | zero => simp [clockGeom]
  | succ R ih =>
      rw [clockGeom]
      have hnonneg := clockGeom_nonneg hr0 R
      have hmul : r * clockGeom r R ≤ clockGeom r R :=
        mul_le_of_le_one_left hnonneg hr1
      push_cast
      linarith
end FirstPassageLinearTransport
