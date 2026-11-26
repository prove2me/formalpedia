-- Prove2me | solution 1 for FirstPassageLinearTransport.completed_oddCount_centered_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:20:27.5628+00:00
-- url     : https://prove2.me/submissions/8480bb64-35f9-492a-84bc-52b6dcb6915e

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_firstBadLandingEnvelope
import Theorems.Thm_FirstPassageLinearTransport_mem_generatedFirstBadSources
import Theorems.Thm_FirstPassageLinearTransport_mem_landingBad
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSourcesAtTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFeasibleTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFirstBadSourcesAtRank
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_timeoutFirstBadSourcesAtRank
import Theorems.Thm_FirstPassageLinearTransport_mem_timeoutHighFirstBadSourcesAtRank
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_add
import Theorems.Thm_FirstPassageLinearTransport_oddCount_two_pow_eq_zero
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
attribute [local simp] FirstPassageLinearTransport.StageSetup.lowerTolerance_M0
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_scale
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.card_boolSupport_cons
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_firstBadLandingEnvelope
attribute [local simp] FirstPassageLinearTransport.mem_generatedFirstBadSources
attribute [local simp] FirstPassageLinearTransport.mem_landingBad
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSources
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSourcesAtTimes
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_shrinkingFeasibleTimes
attribute [local simp] FirstPassageLinearTransport.mem_shrinkingFirstBadSourcesAtRank
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_timeoutFirstBadSourcesAtRank
attribute [local simp] FirstPassageLinearTransport.mem_timeoutHighFirstBadSourcesAtRank
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.shrinkingHighSetup_M0
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.stoppedBallotValue_cons



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {n elapsed q v S : ℕ} {F : ℝ}
    (heq : orbit elapsed n = 2 ^ q)
    (hvq : v ≤ q) (hvS : v ≤ S)
    (hbase : ∀ j : ℕ, j ≤ elapsed →
      |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤ F) :
    ∀ j : ℕ, j ≤ elapsed + v →
      |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤ F + (S : ℝ) / 2 := by
  intro j hj
  have hF0 : 0 ≤ F := by
    have hzero := hbase 0 (Nat.zero_le elapsed)
    simpa using hzero
  by_cases hjOld : j ≤ elapsed
  · have h := hbase j hjOld
    have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
    nlinarith
  · let u := j - elapsed
    have hjForm : j = elapsed + u := by
      dsimp [u]
      omega
    have huV : u ≤ v := by
      dsimp [u]
      omega
    have huq := huV.trans hvq
    have huS : (u : ℝ) ≤ S := by exact_mod_cast huV.trans hvS
    have hoddZero := oddCount_two_pow_eq_zero huq
    have hsplit : oddCount n (elapsed + u) = oddCount n elapsed := by
      rw [oddCount_add, heq, hoddZero, add_zero]
    have hbaseElapsed := hbase elapsed le_rfl
    have habs := abs_sub
      ((oddCount n elapsed : ℝ) - (elapsed : ℝ) / 2) ((u : ℝ) / 2)
    rw [hjForm, hsplit]
    push_cast
    have hu0 : (0 : ℝ) ≤ u := Nat.cast_nonneg u
    rw [show (oddCount n elapsed : ℝ) -
        ((elapsed : ℝ) + (u : ℝ)) / 2 =
          ((oddCount n elapsed : ℝ) - (elapsed : ℝ) / 2) -
            (u : ℝ) / 2 by ring]
    calc
      _ ≤ |(oddCount n elapsed : ℝ) - (elapsed : ℝ) / 2| +
          |(u : ℝ) / 2| := habs
      _ = |(oddCount n elapsed : ℝ) - (elapsed : ℝ) / 2| +
          (u : ℝ) / 2 := by rw [abs_of_nonneg (div_nonneg hu0 (by norm_num))]
      _ ≤ F + (S : ℝ) / 2 := by linarith
end FirstPassageLinearTransport
