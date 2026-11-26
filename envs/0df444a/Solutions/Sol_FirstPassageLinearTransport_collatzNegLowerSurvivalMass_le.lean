-- Prove2me | solution 1 for FirstPassageLinearTransport.collatzNegLowerSurvivalMass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:04.504177+00:00
-- url     : https://prove2.me/submissions/dbd88ac0-6a28-45de-8670-a7d2e5cb3ec4

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_lowerSurvivalMass_le_centered
import Theorems.Thm_FirstPassageLinearTransport_collatzTilt_pos
import Theorems.Thm_FirstPassageLinearTransport_collatzTilt_lt_one
import Theorems.Thm_FirstPassageLinearTransport_collatzLogIncrement_abs_le_one
import Theorems.Thm_FirstPassageLinearTransport_collatzLogIncrement_centered
import Theorems.Thm_FirstPassageLinearTransport_collatzTiltVariance_pos
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {B : ℝ} (hB : 0 ≤ B) {n : ℕ} (hn : 0 < n) :
    lowerSurvivalMass collatzTilt
        (fun b ↦ -collatzLogIncrement b) (-B) n 0 ≤
      (1 + 2 / collatzTiltVariance) * (B + 1) / Real.sqrt n := by
  apply lowerSurvivalMass_le_centered
    collatzTilt_pos.le collatzTilt_lt_one.le collatzTiltVariance_pos hB
      (x := fun b ↦ -collatzLogIncrement b)
  · intro b
    simpa only [abs_neg] using collatzLogIncrement_abs_le_one b
  · have hcenter := collatzLogIncrement_centered
    unfold bernoulliAverage at hcenter ⊢
    linarith
  · unfold collatzTiltVariance
    congr 1 <;> ring
  · exact hn
end FirstPassageLinearTransport
