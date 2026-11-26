-- Prove2me | solution 1 for FirstPassageLinearTransport.weightedSurvivalWordMass_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:32.065144+00:00
-- url     : https://prove2.me/submissions/ddffe1f2-21d6-4a18-afd9-b6a11120a081

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
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
    (p : ℝ) (x : Bool → ℝ) (lo : ℝ) (r : ℕ) (z : ℝ) :
    weightedSurvivalWordMass p x lo (r + 1) z =
      if lo ≤ z then bernoulliAverage p
        (weightedSurvivalWordMass p x lo r (z + x false))
        (weightedSurvivalWordMass p x lo r (z + x true))
      else 0 := by
  classical
  rw [weightedSurvivalWordMass]
  rw [← Equiv.sum_comp
    (Fin.consEquiv (fun _ : Fin (r + 1) => Bool))]
  rw [Fintype.sum_prod_type]
  by_cases hz : lo ≤ z
  · simp [Fin.consEquiv, wordSurvivesFrom, hz, bernoulliWordWeight_cons,
      weightedSurvivalWordMass, bernoulliAverage, Finset.mul_sum]
    ring
  · simp [Fin.consEquiv, wordSurvivesFrom, hz]
end FirstPassageLinearTransport
