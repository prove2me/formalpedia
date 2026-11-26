-- Prove2me | solution 1 for FirstPassageLinearTransport.scheduleDensityLower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:45:12.872684+00:00
-- url     : https://prove2.me/submissions/f967ec25-ea87-41a8-a1d6-7fac57023f70

import Definitions.Def_FirstPassageLinearTransport_GlobalAssembly
import Definitions.Def_FirstPassageLinearTransport_BootstrapSchedule
import Theorems.Thm_FirstPassageLinearTransport_rpowLogScheduleIdentity
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageCount_le
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
    {chi Dc omega : ℝ} (hchi0 : 0 < chi) (hchi1 : chi ≤ 1)
    (hDc0 : 0 ≤ Dc) (homega0 : 0 ≤ omega) (M : ℕ) :
    Dc * ((M : ℝ) + 4) ^ (-densityGamma omega chi) ≤
      bootstrapD chi Dc (stageCount omega M) := by
  have hM4 : (0 : ℝ) < (M : ℝ) + 4 := by positivity
  have hR := stageCount_le homega0 M
  have hp : chi ^ (omega * Real.log ((M : ℝ) + 4)) ≤
      chi ^ (stageCount omega M : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hchi0 hchi1 hR
  rw [rpowLogScheduleIdentity hchi0 hM4,
    Real.rpow_natCast] at hp
  simpa [bootstrapD] using mul_le_mul_of_nonneg_left hp hDc0
end FirstPassageLinearTransport
