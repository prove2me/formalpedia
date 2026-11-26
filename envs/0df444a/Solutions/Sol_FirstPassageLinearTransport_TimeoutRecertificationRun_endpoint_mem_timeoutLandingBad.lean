-- Prove2me | solution 1 for FirstPassageLinearTransport.TimeoutRecertificationRun.endpoint_mem_timeoutLandingBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:09:37.694476+00:00
-- url     : https://prove2.me/submissions/cadb0cf5-a20f-44f2-8cbf-cfe5d20f04e5

import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
import Definitions.Def_FirstPassageLinearTransport_TimeoutFirstBad
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_landingBand
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
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_not_lowStageTimeout_two_pow_succ
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
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
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
noncomputable section
namespace FirstPassageLinearTransport
namespace TimeoutRecertificationRun
theorem _root_.solution
    {P : TimeoutHighRunData} {K₀ : ℝ}
    {L M S n elapsed p : ℕ}
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed p)
    (hp : 1 ≤ p)
    (hnextPos : 0 < timeoutTargetRank K₀ L (p - 1))
    (hnextLt : timeoutTargetRank K₀ L (p - 1) < p)
    (htimeout : LowStageTimeout K₀ L (p - 1) (orbit elapsed n)) :
    orbit elapsed n ∈ timeoutLandingBad K₀ L p := by
  classical
  have hband := hrun.landingBand
  have hne : orbit elapsed n ≠ 2 ^ p := by
    intro heq
    have hnot := not_lowStageTimeout_two_pow_succ
      (m := p - 1) hnextPos (by simpa [Nat.sub_add_cancel hp] using hnextLt)
    apply hnot
    simpa [heq, Nat.sub_add_cancel hp] using htimeout
  have hlower : 2 ^ (p - 1) ≤ orbit elapsed n := by
    have hmul : 2 ^ (p - 1) * 2 < orbit elapsed n * 2 := by
      calc
        2 ^ (p - 1) * 2 = 2 ^ ((p - 1) + 1) := by rw [pow_succ]
        _ = 2 ^ p := by rw [Nat.sub_add_cancel hp]
        _ < 2 * orbit elapsed n := hband.1
        _ = orbit elapsed n * 2 := by omega
    exact (lt_of_mul_lt_mul_right hmul (by norm_num)).le
  have hupper : orbit elapsed n < 2 ^ p := lt_of_le_of_ne hband.2 hne
  rw [timeoutLandingBad, Finset.mem_filter, mem_dyadicShell]
  exact ⟨⟨hlower, by simpa [Nat.sub_add_cancel hp] using hupper⟩, htimeout⟩
end TimeoutRecertificationRun
end FirstPassageLinearTransport
