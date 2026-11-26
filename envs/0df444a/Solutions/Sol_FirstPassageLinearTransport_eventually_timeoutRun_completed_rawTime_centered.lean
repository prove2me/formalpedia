-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_timeoutRun_completed_rawTime_centered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:22:39.075871+00:00
-- url     : https://prove2.me/submissions/2a97fa16-a117-46f7-8a6c-b7623c3213e2

import Definitions.Def_FirstPassageLinearTransport_TimeoutOrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Theorems.Thm_FirstPassageLinearTransport_rawTime_add_exact_halving
import Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutRun_rawTime_centered
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_a0_lt_one
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_driftGap_lt_a0
import Theorems.Thm_FirstPassageLinearTransport_driftGap_pos
import Theorems.Thm_FirstPassageLinearTransport_eventually_shrinkingSwitchRank_lt_source
import Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutTimePotential_source_le_sqrt
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
import Theorems.Thm_FirstPassageLinearTransport_timeoutTimePotential_nonneg
import Theorems.Thm_FirstPassageLinearTransport_timeout_switch_sq_le_source_potential
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
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A : ℕ → ℝ}
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop) :
    ∀ᶠ M : ℕ in atTop, ∀ {L n elapsed q : ℕ},
      L = movingTerminalRank A M →
      q ≤ shrinkingSwitchRank P.Cswitch M →
      TimeoutRecertificationRun P.run.toTimeoutHigh P.K₀ L M
        (shrinkingSwitchRank P.Cswitch M) n elapsed q →
      orbit elapsed n = 2 ^ q →
      |(2 * driftGap / 3) *
          (rawTime n (elapsed + (q - L)) : ℝ) - (M : ℝ)| ≤
        timeoutCompletedRawClockSupportConstant P.run.toTimeoutHigh P.Cswitch *
          Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
  have hRaw := eventually_timeoutRun_rawTime_centered P hbuffer
  have hPotential := eventually_timeoutTimePotential_source_le_sqrt
    P.run.toTimeoutHigh P.Cswitch_pos.le
  have hSwitch := eventually_shrinkingSwitchRank_lt_source P.Cswitch_pos.le
  filter_upwards [hRaw, hPotential, hSwitch, eventually_ge_atTop (1 : ℕ)]
    with M hRaw hPotential hSwitch hM
  intro L n elapsed q hL hqS hrun heq
  let S := shrinkingSwitchRank P.Cswitch M
  let sourcePotential := timeoutTimePotential P.run.toTimeoutHigh M S (M + 1)
  let root := Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
  have hrun' : TimeoutRecertificationRun P.run.toTimeoutHigh P.K₀
      (movingTerminalRank A M) M (shrinkingSwitchRank P.Cswitch M)
      n elapsed q := by
    simpa [hL] using hrun
  have hRaw' := hRaw hqS hrun'
  have hvq : q - L ≤ q := Nat.sub_le q L
  have htime : rawTime n (elapsed + (q - L)) =
      rawTime n elapsed + (q - L) :=
    rawTime_add_exact_halving heq hvq
  have hSsq : (S : ℝ) ≤ (S : ℝ) ^ 2 := by
    by_cases hS0 : S = 0
    · simp [hS0]
    · have hS1 : (1 : ℝ) ≤ (S : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hS0)
      nlinarith [sq_nonneg ((S : ℝ) - 1)]
  have hreserve : (S : ℝ) ^ 2 ≤ sourcePotential := by
    dsimp [sourcePotential, S]
    exact timeout_switch_sq_le_source_potential P.run.toTimeoutHigh (by omega)
  have hvS : q - L ≤ S := (Nat.sub_le q L).trans hqS
  have hvR : ((q - L : ℕ) : ℝ) ≤ sourcePotential := by
    have hvSR : ((q - L : ℕ) : ℝ) ≤ (S : ℝ) := by exact_mod_cast hvS
    exact hvSR.trans (hSsq.trans hreserve)
  have hcoef0 : 0 ≤ 2 * driftGap / 3 :=
    div_nonneg (mul_nonneg (by norm_num) driftGap_pos.le) (by norm_num)
  have hcoefGap : 2 * driftGap / 3 ≤ driftGap := by
    nlinarith [driftGap_pos]
  have hextra : (2 * driftGap / 3) * ((q - L : ℕ) : ℝ) ≤
      timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch * root := by
    have hfirst : (2 * driftGap / 3) * ((q - L : ℕ) : ℝ) ≤
        sourcePotential := by
      calc
        (2 * driftGap / 3) * ((q - L : ℕ) : ℝ) ≤
            driftGap * ((q - L : ℕ) : ℝ) := by gcongr
        _ ≤ 1 * ((q - L : ℕ) : ℝ) := by
          have hgap_le_one : driftGap ≤ 1 := by
            linarith [driftGap_lt_a0, a0_lt_one]
          gcongr
        _ ≤ sourcePotential := by simpa using hvR
    have hpot0 : 0 ≤ sourcePotential := by
      dsimp [sourcePotential, S]
      exact timeoutTimePotential_nonneg P.run.toTimeoutHigh M
        (shrinkingSwitchRank P.Cswitch M) (M + 1)
    have hscaled : sourcePotential ≤ 2 * sourcePotential / driftGap := by
      rw [le_div_iff₀ driftGap_pos]
      have hgap_le_one : driftGap ≤ 1 := by
        linarith [driftGap_lt_a0, a0_lt_one]
      nlinarith
    calc
      (2 * driftGap / 3) * ((q - L : ℕ) : ℝ) ≤ sourcePotential := hfirst
      _ ≤ 1 + 2 * sourcePotential / driftGap := by linarith
      _ ≤ timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch * root := by
        simpa [sourcePotential, S, root, div_eq_mul_inv, mul_assoc] using hPotential
  calc
    |(2 * driftGap / 3) *
          (rawTime n (elapsed + (q - L)) : ℝ) - (M : ℝ)| =
        |((2 * driftGap / 3) * (rawTime n elapsed : ℝ) - (M : ℝ)) +
          (2 * driftGap / 3) * ((q - L : ℕ) : ℝ)| := by
      rw [htime]
      push_cast
      ring
    _ ≤ |(2 * driftGap / 3) * (rawTime n elapsed : ℝ) - (M : ℝ)| +
          |(2 * driftGap / 3) * ((q - L : ℕ) : ℝ)| := abs_add_le _ _
    _ = |(2 * driftGap / 3) * (rawTime n elapsed : ℝ) - (M : ℝ)| +
          (2 * driftGap / 3) * ((q - L : ℕ) : ℝ) := by
      rw [abs_of_nonneg (mul_nonneg hcoef0 (Nat.cast_nonneg _))]
    _ ≤ timeoutRawClockSupportConstant P.run.toTimeoutHigh P.Cswitch * root +
          timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch * root :=
      add_le_add hRaw' hextra
    _ = timeoutCompletedRawClockSupportConstant P.run.toTimeoutHigh P.Cswitch *
          root := by
      unfold timeoutCompletedRawClockSupportConstant
      ring
end FirstPassageLinearTransport
