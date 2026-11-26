-- Prove2me | solution 1 for FirstPassageLinearTransport.collatzFullThreeBlockMass_le_envelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:58:15.449748+00:00
-- url     : https://prove2.me/submissions/091a9875-cbab-40ed-b431-3b96b6841b7e

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_bernoulliWordWeight_nonneg
import Theorems.Thm_FirstPassageLinearTransport_collatzThreeBlockEnvelopeEvent_of_full
import Theorems.Thm_FirstPassageLinearTransport_collatzThreeBlockEnvelopeIndicator_nonneg
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
    collatzFullThreeBlockMass (1 / 2) a b B q ≤
      collatzThreeBlockFlatMass (1 / 2) a b B q := by
  classical
  unfold collatzFullThreeBlockMass collatzThreeBlockFlatMass
  apply Finset.sum_le_sum
  intro u _hu
  apply Finset.sum_le_sum
  intro w _hw
  apply Finset.sum_le_sum
  intro v _hv
  by_cases hfull : collatzFullBarrierBinEvent B q
      (collatzThreeBlockWord u v w)
  · have henv := collatzThreeBlockEnvelopeEvent_of_full hfull
    simp [collatzFullBarrierBinIndicator, hfull,
      collatzThreeBlockEnvelopeIndicator, henv]
  · simp [collatzFullBarrierBinIndicator, hfull]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (bernoulliWordWeight_nonneg (by norm_num) (by norm_num) u)
          (bernoulliWordWeight_nonneg (by norm_num) (by norm_num) v))
        (bernoulliWordWeight_nonneg (by norm_num) (by norm_num) w))
      (collatzThreeBlockEnvelopeIndicator_nonneg B q u v w)
end FirstPassageLinearTransport
