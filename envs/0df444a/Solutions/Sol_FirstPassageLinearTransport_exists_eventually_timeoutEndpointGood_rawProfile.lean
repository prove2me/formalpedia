-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_eventually_timeoutEndpointGood_rawProfile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:24:51.990348+00:00
-- url     : https://prove2.me/submissions/05d3b169-798c-44d8-9c7b-9e9c04abc828

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointProfile
import Definitions.Def_FirstPassageLinearTransport_RankTransportAsymptotics
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
import Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutDisplacementLoss_le_terminalScale
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_pos
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_card_landingBad_shrinking_high_density_le
import Theorems.Thm_FirstPassageLinearTransport_card_shellInitialWindowBad_shrinking_le
import Theorems.Thm_FirstPassageLinearTransport_driftGap_pos
import Theorems.Thm_FirstPassageLinearTransport_eventually_interval_rankTransport_small
import Theorems.Thm_FirstPassageLinearTransport_eventually_movingLow_admissible
import Theorems.Thm_FirstPassageLinearTransport_eventually_movingTerminalRank_lt_shrinkingSwitchRank
import Theorems.Thm_FirstPassageLinearTransport_eventually_shrinkingSwitchRank_lt_source
import Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutFeasibleTimes_card_lt_sqrt
import Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutTargetRank_admissible
import Theorems.Thm_FirstPassageLinearTransport_exists_card_timeoutShellBad_endpointRate_le
import Theorems.Thm_FirstPassageLinearTransport_firstPassageEndpointRate_pos
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
import Theorems.Thm_FirstPassageLinearTransport_quadraticWindowShellConstant_pos
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shellBad_timeoutEndpointGood
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
import Theorems.Thm_FirstPassageLinearTransport_tendsto_movingLowRatio
import Theorems.Thm_FirstPassageLinearTransport_tendsto_movingTerminalRank_atTop
import Theorems.Thm_FirstPassageLinearTransport_timeoutLandingBad_eq_timeoutShellBad
import Theorems.Thm_FirstPassageLinearTransport_timeoutSeparatedFailureEnvelope_density_sharp_le
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
    (hbuffer : Tendsto (movingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ᶠ M : ℕ in atTop,
        shellExceptionalRatio (timeoutEndpointGood P A M) M ≤
          let L := movingTerminalRank A M
          let H :=
            (timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1) *
              Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
          let dHi := shrinkingHighDensityProfile P.run P.Cswitch M
          let b := firstPassageEndpointRate - D / (L : ℝ)
          dHi + H * (1 + 6 / (P.run.rStar : ℝ)) *
              ((M : ℝ) + 1) ^ 2 * dHi +
            H * (1 + 6 / (P.run.rStar : ℝ)) *
              exactSharpCriticalLowSeriesConstant
                (firstPassageEndpointRate / 2) (C / 2) *
              (Real.sqrt (L + 1) * Real.exp (-(b * (L : ℝ)))) := by
  obtain ⟨C, D, hC, hD, hLowBase⟩ :=
    exists_card_timeoutShellBad_endpointRate_le
      (show 0 ≤ P.K₀ by linarith [P.K₀_gt_six])
  refine ⟨C, D, hC, hD, ?_⟩
  have hTerminalT := tendsto_movingTerminalRank_atTop hbuffer
  have hAdmBase := eventually_movingLow_admissible
    (show 0 < P.K₀ by linarith [P.K₀_gt_six]) P.K₁_pos
  have hAdm := hTerminalT.eventually hAdmBase
  have hTimeoutAdmBase := eventually_timeoutTargetRank_admissible
    (show 0 < P.K₀ by linarith [P.K₀_gt_six])
  have hTimeoutAdm := hTerminalT.eventually hTimeoutAdmBase
  have hScaleBase := eventually_timeoutDisplacementLoss_le_terminalScale P.K₀
  have hScale := hTerminalT.eventually hScaleBase
  have hSmallBase := eventually_interval_rankTransport_small P.run.rStar_pos
  have hSmall := hTerminalT.eventually hSmallBase
  have hLS := eventually_movingTerminalRank_lt_shrinkingSwitchRank
    P.Amax_pos.le P.terminal_below_switch hUpper
  have hSM := eventually_shrinkingSwitchRank_lt_source P.Cswitch_pos.le
  have hTimes := eventually_timeoutFeasibleTimes_card_lt_sqrt
    P.run.toTimeoutHigh P.K₀ P.Cswitch_pos.le
  have hStarHi : P.run.rStar ≤ P.run.rHi := by
    rw [P.run.rStar_eq]
    exact min_le_left _ _
  have hStarLoBase : ∀ᶠ L : ℕ in atTop,
      (P.run.rStar : ℝ) ≤ movingLowRatio P.K₀ L := by
    have hrStarOne : (P.run.rStar : ℝ) < 1 := by
      have hStarHiR : (P.run.rStar : ℝ) ≤ (P.run.rHi : ℝ) := by
        exact_mod_cast hStarHi
      exact hStarHiR.trans_lt P.run.pHi.r_lt_one
    exact (tendsto_movingLowRatio P.K₀).eventually
      (Ici_mem_nhds hrStarOne)
  have hStarLo := hTerminalT.eventually hStarLoBase
  have hRateBase : ∀ᶠ L : ℕ in atTop,
      firstPassageEndpointRate / 2 ≤
        firstPassageEndpointRate - D / (L : ℝ) := by
    have hcast : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun L : ℕ => ((L : ℝ))⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hcast
    have hdiv : Tendsto (fun L : ℕ => D / (L : ℝ)) atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_const_nhds.mul hinv :
          Tendsto (fun L : ℕ => D * ((L : ℝ))⁻¹) atTop (nhds (D * 0)))
    have hrate : Tendsto
        (fun L : ℕ => firstPassageEndpointRate - D / (L : ℝ))
        atTop (nhds firstPassageEndpointRate) := by
      simpa using (tendsto_const_nhds.sub hdiv)
    exact hrate.eventually (Ici_mem_nhds (by
      linarith [firstPassageEndpointRate_pos]))
  have hRate := hTerminalT.eventually hRateBase
  have hRank2 := (tendsto_atTop.1 hTerminalT) 2
  filter_upwards [hAdm, hTimeoutAdm, hScale, hSmall, hLS, hSM, hTimes,
      hStarLo, hRate, hRank2,
      eventually_ge_atTop (max 2 P.run.pHi.M0)]
    with M hAdm hTimeoutAdm hScale hSmall hLS hSM hTimes hStarLo hRate
      hRank2 hM
  let L := movingTerminalRank A M
  let S := shrinkingSwitchRank P.Cswitch M
  let H :=
    (timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1) *
      Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
  let dHi := shrinkingHighDensityProfile P.run P.Cswitch M
  let b := firstPassageEndpointRate - D / (L : ℝ)
  have hM1 : 1 ≤ M := by omega
  have hL2 : 2 ≤ L := by simpa [L] using hRank2
  have hLS' : L + 1 ≤ S := by simpa [L, S] using hLS
  have hSM' : S < M := by simpa [S] using hSM
  have hH0 : 0 ≤ H := by
    dsimp [H, timeoutTimeSupportConstant]
    have hrHi0 : 0 < (P.run.rHi : ℝ) := P.run.pHi.r_pos
    have hsqrt1 : Real.sqrt (P.run.rHi : ℝ) < 1 := by
      nlinarith [Real.sq_sqrt hrHi0.le, Real.sqrt_nonneg (P.run.rHi : ℝ),
        P.run.pHi.r_lt_one]
    have hden : 0 < 1 - Real.sqrt (P.run.rHi : ℝ) := sub_pos.mpr hsqrt1
    have hnum : 0 ≤ P.run.D + P.run.tau + 3 := by
      linarith [P.run.D_pos, P.run.pHi.eta_pos]
    have hinner : 0 ≤
        (P.run.D + P.run.tau + 3) /
            (1 - Real.sqrt (P.run.rHi : ℝ)) +
          (P.Cswitch + 5) ^ 2 := by positivity
    have hratio : 0 ≤ 2 / driftGap :=
      div_nonneg (by norm_num) driftGap_pos.le
    positivity
  have hC2 : 0 ≤ C / 2 := by positivity
  have hb₀ : 0 < firstPassageEndpointRate / 2 :=
    div_pos firstPassageEndpointRate_pos (by norm_num)
  have hTimes' : ∀ q ∈ Finset.Icc L (M - 1),
      ((timeoutFeasibleTimes P.run.toTimeoutHigh P.K₀ L M S q).card : ℝ) ≤ H := by
    intro q hq
    exact (hTimes L q).le
  have hInitial :
      ((shellInitialWindowBad M
        (timeoutHighTolerance P.run.toTimeoutHigh M M)).card : ℝ) /
          (2 : ℝ) ^ M ≤ dHi := by
    have hbase := card_shellInitialWindowBad_shrinking_le P.run
      P.Cswitch_pos P.high_cap hM1 hSM.le
    dsimp [dHi, shrinkingHighDensityProfile]
    have hboundary : 0 ≤
        Real.exp (-(Real.log 2 * (shrinkingSwitchRank P.Cswitch M : ℝ))) :=
      Real.exp_pos _ |>.le
    simpa [timeoutHighTolerance, shrinkingHighTolerance,
      ShrinkingBarrierRunData.toTimeoutHigh] using (show
      ((shellInitialWindowBad M
        (shrinkingHighTolerance P.run M M)).card : ℝ) / (2 : ℝ) ^ M ≤
          Real.exp (-(Real.log 2 * (shrinkingSwitchRank P.Cswitch M : ℝ))) +
            quadraticWindowShellConstant *
              Real.exp (-(maximalBarrierC0 * P.run.D ^ 2 *
                Real.log ((M : ℝ) + 2))) by linarith)
  have hHighTargets : ∀ q ∈ Finset.Icc (S + 1) (M - 1),
      ((landingBad q
        (timeoutHighTolerance P.run.toTimeoutHigh M (q - 1))).card : ℝ) /
          (2 : ℝ) ^ q ≤ dHi := by
    intro q hq
    have hqLower := (Finset.mem_Icc.mp hq).1
    have hq1 : 1 ≤ q := by omega
    have hSParent : shrinkingSwitchRank P.Cswitch M ≤ q - 1 := by
      simpa [S] using (show S ≤ q - 1 by omega)
    have hbase := card_landingBad_shrinking_high_density_le P.run
      P.Cswitch_pos P.high_cap hq1 hSParent
    have hqS : (S : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show S ≤ q by omega)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hexp : Real.exp (-(Real.log 2 * (q : ℝ))) ≤
        Real.exp (-(Real.log 2 * (S : ℝ))) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    dsimp [dHi, shrinkingHighDensityProfile]
    simpa [S, timeoutHighTolerance, shrinkingHighTolerance,
      ShrinkingBarrierRunData.toTimeoutHigh] using hbase.trans (by
      calc
        _ ≤ Real.exp (-(Real.log 2 * (S : ℝ))) +
            quadraticWindowShellConstant / 2 *
              Real.exp (-(maximalBarrierC0 * P.run.D ^ 2 *
                Real.log ((M : ℝ) + 2))) := add_le_add hexp le_rfl
        _ ≤ Real.exp (-(Real.log 2 * (S : ℝ))) +
            quadraticWindowShellConstant *
              Real.exp (-(maximalBarrierC0 * P.run.D ^ 2 *
                Real.log ((M : ℝ) + 2))) := by
          gcongr
          linarith [quadraticWindowShellConstant_pos])
  have hLow : ∀ p ∈ Finset.Icc (L + 1) S,
      ((timeoutLandingBad P.K₀ L p).card : ℝ) / (2 : ℝ) ^ p ≤
        ((C / 2) / Real.sqrt ((p - 1 : ℕ) : ℝ)) *
          Real.exp (-(b * ((p - 1 : ℕ) : ℝ))) := by
    intro p hp
    have hpI := Finset.mem_Icc.mp hp
    have hLm : L ≤ p - 1 := by omega
    have hbase := hLowBase L (p - 1) (by omega) hLm
      hAdm.2.2.1.le hAdm.2.2.2.1.le hScale
    have hp1 : 1 ≤ p := by omega
    have hpowp : (2 : ℝ) ^ p = (2 : ℝ) ^ (p - 1) * 2 := by
      conv_lhs => rw [show p = (p - 1) + 1 by omega]
      rw [pow_succ]
    rw [timeoutLandingBad_eq_timeoutShellBad]
    calc
      ((timeoutShellBad P.K₀ L (p - 1)).card : ℝ) / (2 : ℝ) ^ p =
          (((timeoutShellBad P.K₀ L (p - 1)).card : ℝ) /
            (2 : ℝ) ^ (p - 1)) / 2 := by
        rw [hpowp]
        ring
      _ ≤ (((C / Real.sqrt ((p - 1 : ℕ) : ℝ)) *
          Real.exp (-(((p - 1 : ℕ) : ℝ) *
            (firstPassageEndpointRate - D / (L : ℝ))))) / 2) := by
        gcongr
      _ = ((C / 2) / Real.sqrt ((p - 1 : ℕ) : ℝ)) *
          Real.exp (-(b * ((p - 1 : ℕ) : ℝ))) := by
        dsimp [b]
        ring
  have hProfile := timeoutSeparatedFailureEnvelope_density_sharp_le
    P.run.rStar_pos hStarHi hStarLo hM1 hLS' hSM' hL2 hH0 hC2
    (fun p hp => (hTimeoutAdm (p - 1) (by
      have hpI := Finset.mem_Icc.mp hp
      omega)).1)
    (fun p hp => by
      have hpI := Finset.mem_Icc.mp hp
      exact (hTimeoutAdm (p - 1) (by omega)).2.trans (by omega))
    (fun q hq => hSmall (M - 1) q hq) hTimes' hInitial hHighTargets
    hLow hb₀ hRate
  rw [shellExceptionalRatio, shellBad_timeoutEndpointGood P A M]
  simpa [L, S, H, dHi, b] using hProfile
end FirstPassageLinearTransport
