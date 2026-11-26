-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_timeoutEndpointRawProfile_le_shellError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:17:37.334158+00:00
-- url     : https://prove2.me/submissions/a5221503-1d66-4d5f-938a-274f7b1aac31

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointProfile
import Definitions.Def_FirstPassageLinearTransport_RankTransportAsymptotics
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
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
import Theorems.Thm_FirstPassageLinearTransport_driftGap_pos
import Theorems.Thm_FirstPassageLinearTransport_eventually_movingEndpointRawProfile_le_shellError
import Theorems.Thm_FirstPassageLinearTransport_exactSharpCriticalLowSeriesConstant_spec
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
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
import Theorems.Thm_FirstPassageLinearTransport_tendsto_movingTerminalRank_atTop
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
    {A : ℕ → ℝ} {C D : ℝ}
    (hC : 0 < C) (hD : 0 < D)
    (hbuffer : Tendsto (movingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax) :
    ∀ᶠ M : ℕ in atTop,
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
          (Real.sqrt (L + 1) * Real.exp (-(b * (L : ℝ)))) ≤
        timeoutEndpointProfileConstant P C D *
          ((2 : ℝ) ^ (-(movingRankBuffer A M)) +
            (((M : ℝ) + 2) ^ (-P.epsilon))) := by
  have hScalar := eventually_movingEndpointRawProfile_le_shellError
    P hC hD hbuffer hUpper
  have hTerminalT := tendsto_movingTerminalRank_atTop hbuffer
  have hRank1 := (tendsto_atTop.1 hTerminalT) 1
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
  filter_upwards [hScalar, hRank1, hRate] with M hScalar hRank1 hRate
  let x : ℝ := (M : ℝ) + 2
  let L : ℕ := movingTerminalRank A M
  let H :=
    (timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1) *
      Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
  let dHi := shrinkingHighDensityProfile P.run P.Cswitch M
  let b := firstPassageEndpointRate - D / (L : ℝ)
  let R := 1 + 6 / (P.run.rStar : ℝ)
  let Q := exactSharpCriticalLowSeriesConstant
    (firstPassageEndpointRate / 2) (C / 2)
  let E := Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))
  let Etimeout := Real.sqrt (L + 1) * Real.exp (-(b * (L : ℝ)))
  let Edy := ((L + 1 : ℕ) : ℝ) *
    Real.exp (-(Real.log 2 * (L : ℝ)))
  let Ahi := dHi + H * R * ((M : ℝ) + 1) ^ 2 * dHi
  have hL1 : 1 ≤ L := by simpa [L] using hRank1
  have hb : 0 < b := by
    dsimp [b, L]
    linarith [firstPassageEndpointRate_pos]
  have hsqrt : Real.sqrt (L + 1) ≤ 2 * Real.sqrt L := by
    have hcast : (L : ℝ) + 1 ≤ 4 * (L : ℝ) := by
      exact_mod_cast (show L + 1 ≤ 4 * L by omega)
    calc
      Real.sqrt (L + 1) ≤ Real.sqrt (4 * (L : ℝ)) :=
        Real.sqrt_le_sqrt hcast
      _ = Real.sqrt (4 : ℝ) * Real.sqrt L := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      _ = 2 * Real.sqrt L := by
        have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
          rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
        rw [hsqrt4]
  have hexp : Real.exp (-(b * (L : ℝ))) ≤
      Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hsub : ((L - 1 : ℕ) : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast Nat.sub_le L 1
    nlinarith
  have htimeout : Etimeout ≤ 2 * E := by
    dsimp [Etimeout, E]
    calc
      Real.sqrt (L + 1) * Real.exp (-(b * (L : ℝ))) ≤
          (2 * Real.sqrt L) * Real.exp (-(b * (L : ℝ))) := by
        gcongr
      _ ≤ (2 * Real.sqrt L) *
          Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) := by
        gcongr
      _ = 2 * (Real.sqrt L *
          Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) := by ring
  have hT0 : 0 ≤ timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1 := by
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
    dsimp [timeoutTimeSupportConstant]
    have hratio : 0 ≤ 2 / driftGap :=
      div_nonneg (by norm_num) driftGap_pos.le
    nlinarith [mul_nonneg hratio hinner]
  have hH0 : 0 ≤ H := by
    dsimp [H]
    exact mul_nonneg hT0 (Real.sqrt_nonneg _)
  have hR0 : 0 ≤ R := by
    have hr : (0 : ℝ) < (P.run.rStar : ℝ) := by
      exact_mod_cast P.run.rStar_pos
    dsimp [R]
    positivity
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    exact (exactSharpCriticalLowSeriesConstant_spec
      (div_pos firstPassageEndpointRate_pos (by norm_num))
      (by positivity : 0 ≤ C / 2)).1.le
  have hdHi0 : 0 ≤ dHi := by
    dsimp [dHi, shrinkingHighDensityProfile]
    have hquad := quadraticWindowShellConstant_pos.le
    positivity
  have hAhi0 : 0 ≤ Ahi := by
    dsimp [Ahi]
    positivity
  have hHQ0 : 0 ≤ H * R * Q := by positivity
  have hlowMul : H * R * Q * Etimeout ≤ H * R * Q * (2 * E) :=
    mul_le_mul_of_nonneg_left htimeout hHQ0
  have hOldLower : Ahi + H * R * Q * E ≤
      Ahi + H * R * Q * (Edy + E) := by
    have hEdy0 : 0 ≤ Edy := by dsimp [Edy]; positivity
    exact add_le_add (le_refl Ahi)
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hEdy0) hHQ0)
  have hCompare : Ahi + H * R * Q * Etimeout ≤
      2 * (Ahi + H * R * Q * (Edy + E)) := by
    calc
      Ahi + H * R * Q * Etimeout ≤
          Ahi + H * R * Q * (2 * E) := add_le_add (le_refl Ahi) hlowMul
      _ = Ahi + 2 * (H * R * Q * E) := by ring
      _ ≤ 2 * (Ahi + H * R * Q * E) := by linarith
      _ ≤ 2 * (Ahi + H * R * Q * (Edy + E)) := by gcongr
  have hScalar2 := mul_le_mul_of_nonneg_left hScalar (by norm_num : (0 : ℝ) ≤ 2)
  dsimp only
  calc
    dHi + H * R * ((M : ℝ) + 1) ^ 2 * dHi +
        H * R * Q * Etimeout = Ahi + H * R * Q * Etimeout := by rfl
    _ ≤ 2 * (Ahi + H * R * Q * (Edy + E)) := hCompare
    _ ≤ 2 * (movingEndpointProfileConstant P C D *
        ((2 : ℝ) ^ (-(movingRankBuffer A M)) + x ^ (-P.epsilon))) := by
      simpa [Ahi, H, R, Q, E, Edy, L, b, x, dHi,
        timeoutTimeSupportConstant, movingTimeSupportConstant,
        ShrinkingBarrierRunData.toTimeoutHigh] using hScalar2
    _ = timeoutEndpointProfileConstant P C D *
        ((2 : ℝ) ^ (-(movingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-P.epsilon))) := by
      dsimp [timeoutEndpointProfileConstant, x]
      ring
end FirstPassageLinearTransport
