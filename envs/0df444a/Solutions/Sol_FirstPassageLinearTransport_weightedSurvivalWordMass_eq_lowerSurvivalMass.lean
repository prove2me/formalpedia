-- Prove2me | solution 1 for FirstPassageLinearTransport.weightedSurvivalWordMass_eq_lowerSurvivalMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:56:24.537631+00:00
-- url     : https://prove2.me/submissions/4d291ca4-463f-4d34-b34d-62de60a9615c

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_weightedSurvivalWordMass_succ
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
    (p : ℝ) (x : Bool → ℝ) (lo : ℝ) :
    ∀ r z, weightedSurvivalWordMass p x lo r z =
      lowerSurvivalMass p x lo r z := by
  intro r
  induction r with
  | zero =>
      intro z
      by_cases hz : lo ≤ z <;>
        simp [weightedSurvivalWordMass, bernoulliWordWeight,
          wordSurvivesFrom, lowerSurvivalMass, hz]
  | succ r ihr =>
      intro z
      rw [weightedSurvivalWordMass_succ, lowerSurvivalMass]
      split
      · rw [ihr, ihr]
      · rfl
end FirstPassageLinearTransport
