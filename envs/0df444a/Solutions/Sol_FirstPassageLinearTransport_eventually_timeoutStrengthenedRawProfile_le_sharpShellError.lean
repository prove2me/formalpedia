-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_timeoutStrengthenedRawProfile_le_sharpShellError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:17:28.109151+00:00
-- url     : https://prove2.me/submissions/7db4b3a9-b6bf-4ea3-b50c-b6f772f35c76

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
import Theorems.Thm_FirstPassageLinearTransport_eventually_sqrtSupport_mul_quadratic_rpow_le_power
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
import Theorems.Thm_FirstPassageLinearTransport_sharp_timeout_scalar_le_buffer
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighDensityProfile_le_rpow
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
import Theorems.Thm_FirstPassageLinearTransport_tendsto_movingTerminalRank_atTop_of_sharp
import Theorems.Thm_FirstPassageLinearTransport_weightedTailConstant_pos
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
    {A R : ℕ → ℝ} {D : ℝ}
    (hD : 0 < D)
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop) :
    ∀ᶠ M : ℕ in atTop,
      let L := movingTerminalRank A M
      let H :=
        (timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1) *
          Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))
      let dHi := shrinkingHighDensityProfile P.run P.Cswitch M
      dHi + H * (1 + 6 / (P.run.rStar : ℝ)) *
          ((M : ℝ) + 1) ^ 2 * dHi +
        H * (1 + 6 / (P.run.rStar : ℝ)) *
          (3 * (D / 2) * weightedTailConstant
            firstPassageEndpointRate (firstPassageEndpointRate / 2)) *
          ((1 / Real.sqrt L) *
            Real.exp (-(firstPassageEndpointRate * (L : ℝ)))) +
        4 / R M ≤
      sharpTimeoutEndpointProfileConstant P D *
          ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
            (((M : ℝ) + 2) ^ (-P.epsilon))) +
        4 / R M := by
  let pHi := min (P.Cswitch * Real.log 2)
    (maximalBarrierC0 * P.run.D ^ 2)
  let K := 1 + quadraticWindowShellConstant
  let T := timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch + 1
  let G := 1 + 6 / (P.run.rStar : ℝ)
  let Q := 3 * (D / 2) * weightedTailConstant
    firstPassageEndpointRate (firstPassageEndpointRate / 2)
  let B := Real.sqrt (2 * firstPassageEndpointRate)
  have hHighBase := eventually_sqrtSupport_mul_quadratic_rpow_le_power
    (p := pHi) (kappa := P.epsilon) (by
      simpa [pHi] using P.high_rate_margin)
  have hTerminalT := tendsto_movingTerminalRank_atTop_of_sharp hbuffer
  have hRank1 := (tendsto_atTop.1 hTerminalT) 1
  have hBuf0 := (tendsto_atTop.1 hbuffer) 0
  filter_upwards [hHighBase, hRank1, hBuf0]
    with M hHighBase hRank1 hBuf0
  let x : ℝ := (M : ℝ) + 2
  let L : ℕ := movingTerminalRank A M
  let dHi := shrinkingHighDensityProfile P.run P.Cswitch M
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hK0 : 0 ≤ K := by
    dsimp [K]
    linarith [quadraticWindowShellConstant_pos]
  have hT0 : 0 ≤ T := by
    have hrHi0 : 0 < (P.run.rHi : ℝ) := P.run.pHi.r_pos
    have hsqrtSq := Real.sq_sqrt hrHi0.le
    have hsqrt0 := Real.sqrt_nonneg (P.run.rHi : ℝ)
    have hsqrt1 : Real.sqrt (P.run.rHi : ℝ) < 1 := by
      nlinarith [P.run.pHi.r_lt_one]
    have hden : 0 < 1 - Real.sqrt (P.run.rHi : ℝ) := sub_pos.mpr hsqrt1
    have hnum : 0 ≤ P.run.D + P.run.tau + 3 := by
      linarith [P.run.D_pos, P.run.pHi.eta_pos]
    have hinner : 0 ≤
        (P.run.D + P.run.tau + 3) /
            (1 - Real.sqrt (P.run.rHi : ℝ)) +
          (P.Cswitch + 5) ^ 2 := by positivity
    have hratio : 0 ≤ 2 / driftGap :=
      div_nonneg (by norm_num) driftGap_pos.le
    dsimp [T, timeoutTimeSupportConstant,
      ShrinkingBarrierRunData.toTimeoutHigh]
    positivity
  have hG0 : 0 ≤ G := by
    have hr : (0 : ℝ) < (P.run.rStar : ℝ) := by
      exact_mod_cast P.run.rStar_pos
    dsimp [G]
    positivity
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    have htail : 0 < weightedTailConstant firstPassageEndpointRate
        (firstPassageEndpointRate / 2) :=
      weightedTailConstant_pos
        (by linarith [firstPassageEndpointRate_pos])
        (by linarith [firstPassageEndpointRate_pos])
    positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hdHi : dHi ≤ K * x ^ (-pHi) := by
    simpa [dHi, K, x, pHi] using
      shrinkingHighDensityProfile_le_rpow P.run P.Cswitch M
  have hdHi0 : 0 ≤ dHi := by
    dsimp [dHi, shrinkingHighDensityProfile]
    have hquad : 0 ≤ quadraticWindowShellConstant :=
      quadraticWindowShellConstant_pos.le
    positivity
  have hDirectPower : x ^ (-pHi) ≤ x ^ (-P.epsilon) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by
      have hmargin := P.high_rate_margin
      dsimp [pHi] at hmargin ⊢
      linarith)
  have hDirect : dHi ≤ K * x ^ (-P.epsilon) :=
    hdHi.trans (mul_le_mul_of_nonneg_left hDirectPower hK0)
  have hHighTerm :
      T * Real.sqrt (x * Real.log x) * G *
          (((M : ℝ) + 1) ^ 2 * dHi) ≤
        (T * G * K) * x ^ (-P.epsilon) := by
    calc
      _ ≤ T * Real.sqrt (x * Real.log x) * G *
          (((M : ℝ) + 1) ^ 2 * (K * x ^ (-pHi))) := by
        gcongr
      _ = T * G * K *
          (Real.sqrt (x * Real.log x) *
            (((M : ℝ) + 1) ^ 2 * x ^ (-pHi))) := by ring
      _ ≤ (T * G * K) * x ^ (-P.epsilon) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa [x, pHi] using hHighBase)
          (mul_nonneg (mul_nonneg hT0 hG0) hK0)
  have hL1 : 1 ≤ L := by simpa [L] using hRank1
  have hLowScalar := sharp_timeout_scalar_le_buffer hBuf0 hRank1
  have hTGQ0 : 0 ≤ T * G * Q :=
    mul_nonneg (mul_nonneg hT0 hG0) hQ0
  have hLowTerm :
      T * Real.sqrt (x * Real.log x) * G * Q *
          ((1 / Real.sqrt L) *
            Real.exp (-(firstPassageEndpointRate * (L : ℝ)))) ≤
        (T * G * Q * B) *
          ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M))) := by
    have hmul := mul_le_mul_of_nonneg_left hLowScalar hTGQ0
    calc
      T * Real.sqrt (x * Real.log x) * G * Q *
            ((1 / Real.sqrt L) *
              Real.exp (-(firstPassageEndpointRate * (L : ℝ)))) =
          (T * G * Q) *
            (Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) *
              (1 / Real.sqrt (movingTerminalRank A M)) *
              Real.exp (-(firstPassageEndpointRate *
                (movingTerminalRank A M : ℝ)))) := by
            dsimp [x, L]
            ring
      _ ≤ (T * G * Q) *
          (Real.sqrt (2 * firstPassageEndpointRate) *
            (2 : ℝ) ^ (-(sharpMovingRankBuffer A M))) := hmul
      _ = (T * G * Q * B) *
          ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M))) := by
        dsimp [B]
        ring
  have hbufTerm0 : 0 ≤ (2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) := by
    positivity
  have hxpow0 : 0 ≤ x ^ (-P.epsilon) := Real.rpow_nonneg hx0.le _
  have hTGK0 : 0 ≤ T * G * K :=
    mul_nonneg (mul_nonneg hT0 hG0) hK0
  have hTGQB0 : 0 ≤ T * G * Q * B :=
    mul_nonneg hTGQ0 hB0
  dsimp only
  calc
    dHi + T * Real.sqrt (x * Real.log x) * G *
          ((M : ℝ) + 1) ^ 2 * dHi +
        T * Real.sqrt (x * Real.log x) * G * Q *
          ((1 / Real.sqrt L) *
            Real.exp (-(firstPassageEndpointRate * (L : ℝ)))) +
        4 / R M ≤
      K * x ^ (-P.epsilon) +
        (T * G * K) * x ^ (-P.epsilon) +
        (T * G * Q * B) *
          ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M))) +
        4 / R M :=
      add_le_add (add_le_add (add_le_add hDirect
        (by simpa [mul_assoc] using hHighTerm)) hLowTerm) le_rfl
    _ ≤ (K + T * G * K + T * G * Q * B) *
          ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
            x ^ (-P.epsilon)) +
        4 / R M := by
      have hmain :
          K * x ^ (-P.epsilon) +
              (T * G * K) * x ^ (-P.epsilon) +
              (T * G * Q * B) *
                ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M))) ≤
            (K + T * G * K + T * G * Q * B) *
              ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
                x ^ (-P.epsilon)) := by
        calc
          _ ≤ K * (2 ^ (-sharpMovingRankBuffer A M) + x ^ (-P.epsilon)) +
              (T * G * K) *
                (2 ^ (-sharpMovingRankBuffer A M) + x ^ (-P.epsilon)) +
              (T * G * Q * B) *
                (2 ^ (-sharpMovingRankBuffer A M) + x ^ (-P.epsilon)) := by
            exact add_le_add
              (add_le_add
                (mul_le_mul_of_nonneg_left
                  (le_add_of_nonneg_left hbufTerm0) hK0)
                (mul_le_mul_of_nonneg_left
                  (le_add_of_nonneg_left hbufTerm0) hTGK0))
              (mul_le_mul_of_nonneg_left
                (le_add_of_nonneg_right hxpow0) hTGQB0)
          _ = _ := by ring
      exact add_le_add hmain le_rfl
    _ = sharpTimeoutEndpointProfileConstant P D *
          ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
            (((M : ℝ) + 2) ^ (-P.epsilon))) +
        4 / R M := by
      rfl
end FirstPassageLinearTransport
