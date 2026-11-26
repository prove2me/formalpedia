-- Prove2me | solution 1 for FirstPassageLinearTransport.rawTime_prefix_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:47:26.608676+00:00
-- url     : https://prove2.me/submissions/282af25a-4b75-4168-8023-02f961b3e0cd

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
import Theorems.Thm_FirstPassageLinearTransport_oddCount_succ
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
theorem _root_.solution {n k i : ℕ} (hi : i ≤ rawTime n k) :
    ∃ j : ℕ, j ≤ k ∧
      (i = rawTime n j ∨
        (j < k ∧ orbit j n % 2 = 1 ∧ i = rawTime n j + 1)) := by
  induction k with
  | zero =>
      have hi0 : i = 0 := by simpa [rawTime] using hi
      exact ⟨0, le_rfl, Or.inl (by simpa [rawTime] using hi0)⟩
  | succ k ih =>
      by_cases hiprev : i ≤ rawTime n k
      · rcases ih hiprev with ⟨j, hjk, hj⟩
        refine ⟨j, hjk.trans (Nat.le_succ k), ?_⟩
        rcases hj with hj | hj
        · exact Or.inl hj
        · exact Or.inr ⟨hj.1.trans_le (Nat.le_succ k), hj.2.1, hj.2.2⟩
      · rcases Nat.mod_two_eq_zero_or_one (orbit k n) with heven | hodd
        · have hbit : (parityBit n k : ℕ) = 0 := by
            simpa [parityBit] using heven
          have htime : rawTime n (k + 1) = rawTime n k + 1 := by
            simp [rawTime, oddCount_succ, hbit]
            omega
          have hiNext : i = rawTime n (k + 1) := by
            rw [htime] at hi
            omega
          exact ⟨k + 1, le_rfl, Or.inl hiNext⟩
        · have hbit : (parityBit n k : ℕ) = 1 := by
            simpa [parityBit] using hodd
          have htime : rawTime n (k + 1) = rawTime n k + 2 := by
            simp [rawTime, oddCount_succ, hbit]
            omega
          have hiCases : i = rawTime n k + 1 ∨
              i = rawTime n (k + 1) := by
            rw [htime] at hi
            omega
          rcases hiCases with hintermediate | hnext
          · exact ⟨k, Nat.le_succ k,
              Or.inr ⟨Nat.lt_succ_self k, hodd, hintermediate⟩⟩
          · exact ⟨k + 1, le_rfl, Or.inl hnext⟩
end FirstPassageLinearTransport
