-- Prove2me | solution 1 for FirstPassageLinearTransport.fixed_polylogarithmic_common_landing_centered_clocks_exact_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:56.745215+00:00
-- url     : https://prove2.me/submissions/d519d9f0-7db1-4528-9ae2-6fb7da3bc01d

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Theorems.Thm_FirstPassageLinearTransport_fixedSharpEndpointMargin_pos
import Theorems.Thm_FirstPassageLinearTransport_tendsto_sharpMovingRankBuffer_const_atTop
import Theorems.Thm_FirstPassageLinearTransport_two_rpow_neg_sharpMovingRankBuffer_const_le
import Theorems.Thm_FirstPassageLinearTransport_moving_polylogarithmic_common_landing_centered_clocks
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_eventually_badCount_assembleDyadic_le_polylog_profile
import Theorems.Thm_FirstPassageLinearTransport_eventually_halfNatLog_profile_le_natLog
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
import Theorems.Thm_FirstPassageLinearTransport_timeSupportCriticalExponent_pos
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
    {A c beta : ℝ}
    (hA : timeSupportCriticalExponent < A)
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
  let q := fixedSharpEndpointMargin A
  have hq : 0 < q := by
    simpa [q] using fixedSharpEndpointMargin_pos hA
  have hA0 : 0 < A := timeSupportCriticalExponent_pos.trans hA
  have hbuffer : Tendsto
      (sharpMovingRankBuffer (fun _ => A)) atTop atTop :=
    tendsto_sharpMovingRankBuffer_const_atTop hA
  obtain ⟨S, C, hC, hDense, hShell, hWitness⟩ :=
    moving_polylogarithmic_common_landing_centered_clocks
      hA0 hc hbeta hq hbuffer (Eventually.of_forall fun _ => le_rfl)
  have hShellPower : ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio S M ≤
        (2 * C) * (((M : ℝ) + 2) ^ (-q)) := by
    filter_upwards [hShell] with M hShell
    have hterm := two_rpow_neg_sharpMovingRankBuffer_const_le hA M
    have hxpow : 0 ≤ ((M : ℝ) + 2) ^ (-q) := by positivity
    dsimp [q] at hterm ⊢
    nlinarith [hC.le]
  rcases (eventually_atTop.1 hShellPower) with ⟨M₀, hM₀⟩
  let B := 2 * C
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hPrefixRaw : ∀ᶠ X : ℕ in atTop,
      (badCount S X : ℝ) ≤
        (1 + 2 * B) * X *
          ((((Nat.log 2 X) / 2 : ℕ) : ℝ) + 2) ^ (-q) := by
    have h := eventually_badCount_assembleDyadic_le_polylog_profile
      (fun _ => S) M₀ B q hB hq.le
      (fun M hM => by
        simpa [B, assembleDyadic] using hM₀ M hM)
    simpa [assembleDyadic] using h
  have hConvert := eventually_halfNatLog_profile_le_natLog hq.le
  let Cexc := (1 + 2 * B) * (2 * Real.log 2) ^ q
  have hCexc : 0 < Cexc := by
    dsimp [Cexc, B]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hCount : ∀ᶠ X : ℕ in atTop,
      (badCount S X : ℝ) ≤
        Cexc * X * (Real.log X) ^ (-q) := by
    filter_upwards [hPrefixRaw, hConvert] with X hRaw hConv
    have hcoef : 0 ≤ (1 + 2 * B) * (X : ℝ) := by positivity
    calc
      (badCount S X : ℝ) ≤
          (1 + 2 * B) * X *
            ((((Nat.log 2 X) / 2 : ℕ) : ℝ) + 2) ^ (-q) := hRaw
      _ ≤ (1 + 2 * B) * X *
          ((2 * Real.log 2) ^ q * (Real.log X) ^ (-q)) := by
            exact mul_le_mul_of_nonneg_left hConv hcoef
      _ = Cexc * X * (Real.log X) ^ (-q) := by
            dsimp [Cexc]
            ring
  refine ⟨S, C, Cexc, hC, hCexc, hDense, ?_, ?_⟩
  · simpa [q] using hCount
  · simpa [q] using hWitness
end FirstPassageLinearTransport
