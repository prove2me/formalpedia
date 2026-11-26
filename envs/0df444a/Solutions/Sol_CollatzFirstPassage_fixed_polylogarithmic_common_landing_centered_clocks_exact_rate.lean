-- Prove2me | solution 1 for CollatzFirstPassage.fixed_polylogarithmic_common_landing_centered_clocks_exact_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:46:03.529547+00:00
-- url     : https://prove2.me/submissions/ea6cbf2d-2f21-4dca-8f98-01896821cd39

import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Definitions.Def_FirstPassageLinearTransport_FixedJointExceptionalOrder
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
import Definitions.Def_FirstPassageLinearTransport_Solution
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_fixed_polylogarithmic_common_landing_centered_clocks_exact_rate
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
import Theorems.Thm_FirstPassageLinearTransport_rawFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcutFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
import Theorems.Thm_FirstPassageLinearTransport_timeSupportCriticalExponent_eq_entropy
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
open CollatzFirstPassage
open Filter
open scoped BigOperators Real Topology
namespace CollatzFirstPassage
theorem _root_.solution
    {A c beta : ℝ}
    (hA : firstPassageCriticalExponent < A)
    (hc : fixedPolylogClockCritical < c)
    (hbeta : 0 < beta) :
    ∃ S : Set ℕ, ∃ C Cexc : ℝ,
      0 < C ∧ 0 < Cexc ∧ NaturalDensityOne S ∧
      (∀ᶠ X : ℕ in atTop,
        (badCount S X : ℝ) ≤
          Cexc * X * (Real.log X) ^
            (-(fixedSharpEndpointMargin A))) ∧
      (∀ᶠ n : ℕ in atTop, n ∈ S →
        ∃ k ell : ℕ,
          (k : ℝ) < c * Real.log n ∧
          |driftGap * (k : ℝ) - (Nat.log 2 n : ℝ)| ≤
            C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          |(2 * driftGap / 3) * (ell : ℝ) - (Nat.log 2 n : ℝ)| ≤
            C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          ell = rawTime n k ∧
          rawOrbit ell n = orbit k n ∧
          (orbit k n : ℝ) < C * (Real.log n) ^ A ∧
          (∀ j : ℕ, j ≤ k →
            (orbit j n : ℝ) ≤
              (n : ℝ) * (((Nat.log 2 n : ℝ) + 2) ^
                (fixedSharpEndpointMargin A))) ∧
          (∀ i : ℕ, i ≤ ell →
            (rawOrbit i n : ℝ) ≤
              (n : ℝ) * (((Nat.log 2 n : ℝ) + 2) ^
                (fixedSharpEndpointMargin A)))) := by
  have horbit : orbit = FirstPassageLinearTransport.orbit := by
    funext k n
    rfl
  have hodd : oddCount = FirstPassageLinearTransport.oddCount := by
    funext n k
    rfl
  have hrawOrbit : rawOrbit = FirstPassageLinearTransport.rawOrbit := by
    funext i n
    rfl
  have hrawTime : rawTime = FirstPassageLinearTransport.rawTime := by
    funext n k
    rfl
  have hbad : badCount = FirstPassageLinearTransport.badCount := by
    funext S X
    rfl
  have hnd : NaturalDensityOne =
      FirstPassageLinearTransport.NaturalDensityOne := by
    funext S
    rfl
  have hgap : driftGap = FirstPassageLinearTransport.driftGap := by rfl
  have hcritical : firstPassageCriticalExponent =
      FirstPassageLinearTransport.timeSupportCriticalExponent := by
    rw [FirstPassageLinearTransport.timeSupportCriticalExponent_eq_entropy]
    rfl
  have hclock : fixedPolylogClockCritical =
      FirstPassageLinearTransport.fixedPolylogClockCritical := by rfl
  have hmargin : fixedSharpEndpointMargin =
      FirstPassageLinearTransport.fixedSharpEndpointMargin := by
    funext A
    unfold fixedSharpEndpointMargin
    unfold FirstPassageLinearTransport.fixedSharpEndpointMargin
    unfold kappaStar binaryEntropyBaseTwo logThreeTwo
    unfold FirstPassageLinearTransport.firstPassageEntropyGap
    unfold FirstPassageLinearTransport.binaryEntropyBaseTwo
    unfold FirstPassageLinearTransport.logThreeTwo
    rfl
  have hA' : FirstPassageLinearTransport.timeSupportCriticalExponent < A := by
    simpa only [hcritical] using hA
  have hc' : FirstPassageLinearTransport.fixedPolylogClockCritical < c := by
    simpa only [hclock] using hc
  simpa only [horbit, hodd, hrawOrbit, hrawTime, hbad, hnd, hgap,
    hmargin] using
    FirstPassageLinearTransport.fixed_polylogarithmic_common_landing_centered_clocks_exact_rate
      hA' hc' hbeta
end CollatzFirstPassage
