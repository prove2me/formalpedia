-- Prove2me | solution 1 for FirstPassageLinearTransport.collatzThreeBlockFlatMass_fair_le_tilt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:58:39.383258+00:00
-- url     : https://prove2.me/submissions/fa63b27c-0c16-4828-890b-fc3b65878f14

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_wordIncrementSum_neg
import Theorems.Thm_FirstPassageLinearTransport_fair_three_word_weight_le
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
    {a b : ℕ} {B q : ℝ} :
    collatzThreeBlockFlatMass (1 / 2) a b B q ≤
      Real.exp (-(collatzFairTiltRate * ((2 * a + b : ℕ) : ℝ)) -
        collatzTiltLambda * (q - B)) *
        collatzThreeBlockFlatMass collatzTilt a b B q := by
  classical
  unfold collatzThreeBlockFlatMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _hu
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w _hw
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _hv
  by_cases hevent : collatzThreeBlockEnvelopeEvent B q u v w
  · have hmid := hevent.2.2
    unfold collatzMiddleInterval at hmid
    have hneg := wordIncrementSum_neg collatzLogIncrement w
    have hterminal : q - B ≤
        wordIncrementSum collatzLogIncrement u +
          wordIncrementSum collatzLogIncrement v +
          wordIncrementSum collatzLogIncrement w := by
      linarith [hmid.1]
    have hw := fair_three_word_weight_le u v w hterminal
    simpa [collatzThreeBlockEnvelopeIndicator, hevent, mul_assoc,
      mul_comm, mul_left_comm] using hw
  · simp [collatzThreeBlockEnvelopeIndicator, hevent]
end FirstPassageLinearTransport
