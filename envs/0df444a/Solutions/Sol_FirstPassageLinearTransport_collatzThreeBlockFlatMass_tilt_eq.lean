-- Prove2me | solution 1 for FirstPassageLinearTransport.collatzThreeBlockFlatMass_tilt_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:56:52.275694+00:00
-- url     : https://prove2.me/submissions/1e9da597-4ca5-4b58-8868-7878799d7725

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
    (a b : ℕ) (B q : ℝ) :
    collatzThreeBlockFlatMass collatzTilt a b B q =
      collatzThreeBlockEnvelopeMass a b B q (q - B) := by
  classical
  unfold collatzThreeBlockFlatMass collatzThreeBlockEnvelopeMass
    weightedSurvivalFactor wordSurvivalIndicator collatzMiddleIntervalMass
    collatzMiddleIntervalIndicator collatzThreeBlockEnvelopeIndicator
    collatzThreeBlockEnvelopeEvent
  apply Finset.sum_congr rfl
  intro u _hu
  by_cases hfirst : wordSurvivesFrom (-B) collatzLogIncrement a 0 u
  · simp only [hfirst, true_and, if_true, mul_one]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _hw
    by_cases hlast : wordSurvivesFrom (-(q + 1))
        (fun bit ↦ -collatzLogIncrement bit) a 0 w
    · simp only [hlast, true_and, if_true, mul_one]
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _hv
      by_cases hmid : collatzMiddleInterval
          (q - B - wordIncrementSum collatzLogIncrement u +
            wordIncrementSum (fun bit ↦ -collatzLogIncrement bit) w) v
      · simp [hmid]
        ring
      · simp [hmid]
    · simp only [hlast, false_and, if_false, mul_zero,
        Finset.sum_const_zero]
      ring
  · simp [hfirst]
end FirstPassageLinearTransport
