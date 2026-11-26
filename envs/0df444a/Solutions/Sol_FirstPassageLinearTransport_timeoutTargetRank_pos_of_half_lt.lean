-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutTargetRank_pos_of_half_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:00:43.195102+00:00
-- url     : https://prove2.me/submissions/877cb1cc-8b97-4d9e-8e9d-83740e75355b

import Definitions.Def_FirstPassageLinearTransport_MovingLowParameters
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
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
open Filter
open scoped Topology
namespace FirstPassageLinearTransport
theorem _root_.solution
    {K₀ : ℝ} {L m : ℕ}
    (hr : (1 / 2 : ℝ) < movingLowRatio K₀ L) (hm : 5 ≤ m) :
    0 < timeoutTargetRank K₀ L m := by
  have hmR : (5 : ℝ) ≤ m := by exact_mod_cast hm
  have hlarge : 2 < movingLowRatio K₀ L * (m : ℝ) := by nlinarith
  have hfloor :
      movingLowRatio K₀ L * (m : ℝ) - 1 <
        (timeoutTargetRank K₀ L m : ℝ) := by
    simpa [timeoutTargetRank] using
      (Nat.sub_one_lt_floor (movingLowRatio K₀ L * (m : ℝ)))
  have : (1 : ℝ) < timeoutTargetRank K₀ L m := by linarith
  have hnat : 1 < timeoutTargetRank K₀ L m := by exact_mod_cast this
  omega
end FirstPassageLinearTransport
