-- Prove2me | solution 1 for FirstPassageLinearTransport.shellBad_timeoutStrengthenedEndpointGood
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:16:43.97983+00:00
-- url     : https://prove2.me/submissions/09208225-3917-45ab-b28c-32b0a8e326cb

import Definitions.Def_FirstPassageLinearTransport_TimeoutExecution
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointParameters
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointProfile
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
open scoped BigOperators Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    (A R : ℕ → ℝ) (M : ℕ) :
    shellBad (timeoutStrengthenedEndpointGood P A R M) M =
      timeoutStrengthenedFailureEnvelope P.run.toTimeoutHigh P.K₀ M
        (movingTerminalRank A M) (shrinkingSwitchRank P.Cswitch M) (R M) := by
  classical
  let L := movingTerminalRank A M
  let S := shrinkingSwitchRank P.Cswitch M
  let E := timeoutSeparatedFailureEnvelope P.run.toTimeoutHigh P.K₀ M L S
  let H := shellMultiplicativeHit M (R M / 4)
  let F := timeoutStrengthenedFailureEnvelope
    P.run.toTimeoutHigh P.K₀ M L S (R M)
  have hEnvelopeShell : ∀ n, n ∈ E → n ∈ dyadicShell M := by
    intro n hn
    dsimp [E] at hn
    unfold timeoutSeparatedFailureEnvelope at hn
    simp only [Finset.mem_union, Finset.mem_biUnion] at hn
    rcases hn with (hn | hn) | hn
    · exact (Finset.mem_filter.mp hn).1
    · rcases hn with ⟨q, _hq, hnq⟩
      exact (mem_timeoutHighFirstBadSourcesAtRank.mp hnq).1
    · rcases hn with ⟨q, _hq, hnq⟩
      exact (mem_timeoutFirstBadSourcesAtRank.mp hnq).1
  have hHeightShell : ∀ n, n ∈ H → n ∈ dyadicShell M := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have hFailureShell : ∀ n, n ∈ F → n ∈ dyadicShell M := by
    intro n hn
    have hn' : n ∈ E ∪ H := by
      simpa [F, E, H, timeoutStrengthenedFailureEnvelope] using hn
    rcases Finset.mem_union.mp hn' with hnE | hnH
    · exact hEnvelopeShell n hnE
    · exact hHeightShell n hnH
  ext n
  rw [shellBad, Finset.mem_filter]
  constructor
  · intro hn
    have hnot : ¬ n ∉ F := by
      simpa [timeoutStrengthenedEndpointGood, F, L, S] using hn.2
    simpa [F] using not_not.mp hnot
  · intro hn
    have hnF : n ∈ F := by simpa [F] using hn
    refine ⟨hFailureShell n hnF, ?_⟩
    simpa [timeoutStrengthenedEndpointGood, F, L, S] using hnF
end FirstPassageLinearTransport
