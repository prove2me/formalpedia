-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutEndpointLiteralNaturalDensityDescent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:43:16.946482+00:00
-- url     : https://prove2.me/submissions/1c4f76c9-ae79-4714-b46f-d8c299d3bd6b

import Definitions.Def_FirstPassageLinearTransport_MovingEndpointAssembly
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointWitness
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
import Theorems.Thm_FirstPassageLinearTransport_timeoutEndpointNaturalDensityDescent
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_log_two_eq_of_mem_dyadicShell
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
import Theorems.Thm_FirstPassageLinearTransport_naturalDensityOne_of_movingShellError
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcutFirstPassageTime_self
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
attribute [local simp] FirstPassageLinearTransport.rawFirstPassageTime_self
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcutFirstPassageTime_self
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
    {A : ℕ → ℝ} {Amax c beta : ℝ}
    (hAmax : 0 < Amax)
    (hc : fixedPolylogClockCritical < c)
    (hbeta : 0 < beta)
    (hbuffer : Tendsto (movingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax) :
    ∃ C eps : ℝ,
      0 < C ∧ 0 < eps ∧
      NaturalDensityOne
        (assembleDyadic (timeoutEndpointWitnessGood A c beta C)) ∧
      (∀ᶠ M : ℕ in atTop,
        shellExceptionalRatio
            (timeoutEndpointWitnessGood A c beta C M) M ≤
          C * ((2 : ℝ) ^ (-(movingRankBuffer A M)) +
            (((M : ℝ) + 2) ^ (-eps)))) ∧
      (∀ n : ℕ,
        n ∈ assembleDyadic (timeoutEndpointWitnessGood A c beta C) →
          ∃ k : ℕ,
            (k : ℝ) < c * Real.log n ∧
            (orbit k n : ℝ) <
              C * (Real.log n) ^ (A (Nat.log 2 n)) ∧
            ∀ j : ℕ, j ≤ k →
              (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta)) := by
  obtain ⟨S, C, eps, hC, heps, hSdense, hShellS, hWitnessS⟩ :=
    timeoutEndpointNaturalDensityDescent hAmax hc hbeta hbuffer hUpper
  rw [eventually_atTop] at hWitnessS
  obtain ⟨N, hWitnessN⟩ := hWitnessS
  have hpowT : Tendsto (fun M : ℕ => (2 : ℝ) ^ M) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hPow := (tendsto_atTop.1 hpowT) (N : ℝ)
  have hShellW : ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio
          (timeoutEndpointWitnessGood A c beta C M) M ≤
        C * ((2 : ℝ) ^ (-(movingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-eps))) := by
    classical
    filter_upwards [hShellS, hPow] with M hShellS hPow
    have hNpow : N ≤ 2 ^ M := by exact_mod_cast hPow
    have hsubset :
        shellBad (timeoutEndpointWitnessGood A c beta C M) M ⊆
          shellBad S M := by
      intro n hn
      rw [shellBad, Finset.mem_filter] at hn ⊢
      refine ⟨hn.1, ?_⟩
      intro hnS
      have hnN : N ≤ n := hNpow.trans (mem_dyadicShell.mp hn.1).1
      have hwitness := hWitnessN n hnN hnS
      have hlog : Nat.log 2 n = M := log_two_eq_of_mem_dyadicShell hn.1
      exact hn.2 (by
        simpa [timeoutEndpointWitnessGood, hlog] using hwitness)
    have hcard :
        ((shellBad (timeoutEndpointWitnessGood A c beta C M) M).card : ℝ) ≤
          ((shellBad S M).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    unfold shellExceptionalRatio at hShellS ⊢
    exact (div_le_div_of_nonneg_right hcard (by positivity)).trans hShellS
  have hDense := naturalDensityOne_of_movingShellError
    (timeoutEndpointWitnessGood A c beta C) heps hbuffer hShellW
  refine ⟨C, eps, hC, heps, hDense, hShellW, ?_⟩
  intro n hn
  simpa [assembleDyadic, timeoutEndpointWitnessGood] using hn
end FirstPassageLinearTransport
