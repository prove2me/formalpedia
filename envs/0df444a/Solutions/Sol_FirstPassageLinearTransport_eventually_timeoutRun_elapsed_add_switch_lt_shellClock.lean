-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_timeoutRun_elapsed_add_switch_lt_shellClock
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:15:50.399234+00:00
-- url     : https://prove2.me/submissions/909af731-9147-4e19-9312-605712ff8f59

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_AsymptoticBounds
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutOrbitCeiling
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_pos
import Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_deviation_add_potential_le
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_deviation_add_potential_le
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_driftGap_pos
import Theorems.Thm_FirstPassageLinearTransport_eventually_shrinkingSwitchRank_envelope_le_shellMargin
import Theorems.Thm_FirstPassageLinearTransport_eventually_sqrt_mul_log_le_linear
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
    (P : MovingEndpointParameterPackage Amax c beta) :
    ∀ᶠ M : ℕ in atTop, ∀ {L n elapsed q : ℕ},
      TimeoutRecertificationRun P.run.toTimeoutHigh P.K₀ L M
        (shrinkingSwitchRank P.Cswitch M) n elapsed q →
      ((elapsed + shrinkingSwitchRank P.Cswitch M : ℕ) : ℝ) <
        c * (M : ℝ) * Real.log 2 := by
  let T := timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch
  let margin := c * Real.log 2 - 1 / driftGap
  have hmargin : 0 < margin := sub_pos.mpr P.clock_pressure
  have hT0 : 0 ≤ T := by
    have hrHi0 : 0 < (P.run.toTimeoutHigh.rHi : ℝ) :=
      P.run.toTimeoutHigh.pHi.r_pos
    have hsqrt1 : Real.sqrt (P.run.toTimeoutHigh.rHi : ℝ) < 1 := by
      nlinarith [Real.sq_sqrt hrHi0.le,
        Real.sqrt_nonneg (P.run.toTimeoutHigh.rHi : ℝ),
        P.run.toTimeoutHigh.pHi.r_lt_one]
    have hden : 0 < 1 - Real.sqrt (P.run.toTimeoutHigh.rHi : ℝ) :=
      sub_pos.mpr hsqrt1
    have hnum : 0 ≤
        P.run.toTimeoutHigh.D + P.run.toTimeoutHigh.tau + 3 := by
      linarith [P.run.toTimeoutHigh.D_pos,
        P.run.toTimeoutHigh.pHi.eta_pos]
    have hinner : 0 ≤
        (P.run.toTimeoutHigh.D + P.run.toTimeoutHigh.tau + 3) /
            (1 - Real.sqrt (P.run.toTimeoutHigh.rHi : ℝ)) +
          (P.Cswitch + 5) ^ 2 := by positivity
    have hratio : 0 ≤ 2 / driftGap :=
      div_nonneg (by norm_num) driftGap_pos.le
    dsimp [T, timeoutTimeSupportConstant]
    nlinarith [mul_nonneg hratio hinner]
  let delta := margin / (8 * (T + 1))
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hSqrt := eventually_sqrt_mul_log_le_linear hdelta
  have hPotential := eventually_timeoutTimePotential_source_le_sqrt
    P.run.toTimeoutHigh P.Cswitch_pos.le
  have hLarge := tendsto_natCast_atTop_atTop.eventually
    (eventually_gt_atTop (4 / (driftGap * margin)))
  have hSwitchMargin := eventually_shrinkingSwitchRank_envelope_le_shellMargin
    P.Cswitch_pos.le (show (0 : ℝ) ≤ 0 by norm_num) (by
      exact half_pos hmargin)
  filter_upwards [hSqrt, hPotential, hLarge, hSwitchMargin,
      eventually_ge_atTop (2 : ℕ)]
    with M hSqrt hPotential hLarge hSwitchMargin hM2
  intro L n elapsed q hrun
  have hM1 : 1 ≤ M := by omega
  let root := Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
  have hpot0 := timeoutTimePotential_nonneg P.run.toTimeoutHigh M
    (shrinkingSwitchRank P.Cswitch M) (M + 1)
  have hdev := hrun.deviation_add_potential_le hM1
  have hpotq0 := timeoutTimePotential_nonneg P.run.toTimeoutHigh M
    (shrinkingSwitchRank P.Cswitch M) q
  have habs :
      |driftGap * (elapsed : ℝ) - (((M + 1 : ℕ) : ℝ) - (q : ℝ))| ≤
        timeoutTimePotential P.run.toTimeoutHigh M
          (shrinkingSwitchRank P.Cswitch M) (M + 1) := by
    linarith
  have hupper := (abs_le.mp habs).2
  have hpotRatio :
      timeoutTimePotential P.run.toTimeoutHigh M
          (shrinkingSwitchRank P.Cswitch M) (M + 1) / driftGap ≤
        T * root := by
    have hratio0 : 0 ≤
        timeoutTimePotential P.run.toTimeoutHigh M
          (shrinkingSwitchRank P.Cswitch M) (M + 1) / driftGap :=
      div_nonneg hpot0 driftGap_pos.le
    calc
      _ ≤ 1 + 2 * (timeoutTimePotential P.run.toTimeoutHigh M
          (shrinkingSwitchRank P.Cswitch M) (M + 1) / driftGap) := by
        linarith
      _ ≤ T * root := by
        simpa [T, root, div_eq_mul_inv, mul_assoc] using hPotential
  have hraw : driftGap * (elapsed : ℝ) ≤
      (M : ℝ) + 1 + timeoutTimePotential P.run.toTimeoutHigh M
        (shrinkingSwitchRank P.Cswitch M) (M + 1) := by
    push_cast at hupper
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    linarith
  have htime : (elapsed : ℝ) ≤ (M : ℝ) / driftGap +
      (1 / driftGap + T * root) := by
    have hdiv : (elapsed : ℝ) ≤ ((M : ℝ) + 1 +
        timeoutTimePotential P.run.toTimeoutHigh M
          (shrinkingSwitchRank P.Cswitch M) (M + 1)) / driftGap := by
      rw [le_div_iff₀ driftGap_pos]
      simpa [mul_comm] using hraw
    calc
      _ ≤ _ := hdiv
      _ = (M : ℝ) / driftGap + (1 / driftGap +
          timeoutTimePotential P.run.toTimeoutHigh M
            (shrinkingSwitchRank P.Cswitch M) (M + 1) / driftGap) := by ring
      _ ≤ (M : ℝ) / driftGap + (1 / driftGap + T * root) := by gcongr
  have hTdelta : T * delta ≤ margin / 8 := by
    have hratioT : T / (T + 1) ≤ 1 :=
      (div_le_one (by positivity)).2 (by linarith)
    calc
      T * delta = (margin / 8) * (T / (T + 1)) := by
        dsimp [delta]
        field_simp
      _ ≤ (margin / 8) * 1 :=
        mul_le_mul_of_nonneg_left hratioT (by positivity)
      _ = margin / 8 := by ring
  have hrootBound : T * root ≤ margin / 4 * (M : ℝ) := by
    have hxM : (M : ℝ) + 2 ≤ 2 * (M : ℝ) := by
      have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM2
      linarith
    have hfirst : T * root ≤ T * (delta * ((M : ℝ) + 2)) :=
      mul_le_mul_of_nonneg_left (by simpa [root] using hSqrt) hT0
    calc
      T * root ≤ (T * delta) * ((M : ℝ) + 2) := by
        simpa [mul_assoc] using hfirst
      _ ≤ (margin / 8) * ((M : ℝ) + 2) :=
        mul_le_mul_of_nonneg_right hTdelta (by positivity)
      _ ≤ (margin / 8) * (2 * (M : ℝ)) :=
        mul_le_mul_of_nonneg_left hxM (by positivity)
      _ = margin / 4 * (M : ℝ) := by ring
  have hconst : 1 / driftGap < margin / 4 * (M : ℝ) := by
    have hprod : 4 / (driftGap * margin) < (M : ℝ) := by simpa using hLarge
    rw [div_lt_iff₀ (mul_pos driftGap_pos hmargin)] at hprod
    rw [div_lt_iff₀ driftGap_pos]
    ring_nf at hprod ⊢
    nlinarith
  have hsublinear : 1 / driftGap + T * root < margin / 2 * (M : ℝ) := by
    linarith
  have hSwitch : (shrinkingSwitchRank P.Cswitch M : ℝ) ≤
      margin / 2 * (M : ℝ) := by
    simpa using hSwitchMargin
  push_cast
  calc
    (elapsed : ℝ) + (shrinkingSwitchRank P.Cswitch M : ℝ) ≤
        ((M : ℝ) / driftGap + (1 / driftGap + T * root)) +
          (shrinkingSwitchRank P.Cswitch M : ℝ) :=
      add_le_add htime (le_refl _)
    _ < (M : ℝ) / driftGap + margin * (M : ℝ) := by linarith
    _ = c * (M : ℝ) * Real.log 2 := by
      dsimp [margin]
      ring
end FirstPassageLinearTransport
