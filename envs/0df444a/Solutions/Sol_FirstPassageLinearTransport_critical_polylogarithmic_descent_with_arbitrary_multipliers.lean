-- Prove2me | solution 1 for FirstPassageLinearTransport.critical_polylogarithmic_descent_with_arbitrary_multipliers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:43:22.665074+00:00
-- url     : https://prove2.me/submissions/447dd4df-d073-4c34-8c7b-2c70ff78951c

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Theorems.Thm_FirstPassageLinearTransport_dyadicShellMinimum_le_of_mem
import Theorems.Thm_FirstPassageLinearTransport_dyadicShellMinimum_pos
import Theorems.Thm_FirstPassageLinearTransport_clippedCriticalMultiplier_pos
import Theorems.Thm_FirstPassageLinearTransport_tendsto_sqrt_dyadicShellMinimum_atTop
import Theorems.Thm_FirstPassageLinearTransport_tendsto_clippedCriticalMultiplier_atTop
import Theorems.Thm_FirstPassageLinearTransport_tendsto_clippedShellHeight_atTop
import Theorems.Thm_FirstPassageLinearTransport_tendsto_sharpMovingRankBuffer_criticalMultiplierExponent
import Theorems.Thm_FirstPassageLinearTransport_eventually_criticalMultiplierExponent_le
import Theorems.Thm_FirstPassageLinearTransport_shellLog_rpow_criticalMultiplierExponent_le
import Theorems.Thm_FirstPassageLinearTransport_two_pow_criticalMultiplierTerminalRank_lt
import Theorems.Thm_FirstPassageLinearTransport_clippedCriticalMultiplier_le_sqrt
import Theorems.Thm_FirstPassageLinearTransport_clippedShellHeight_pos
import Theorems.Thm_FirstPassageLinearTransport_clippedShellHeight_le_of_mem
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
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell_log
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
import Theorems.Thm_FirstPassageLinearTransport_shellPolylogTarget_le_natLog
import Theorems.Thm_FirstPassageLinearTransport_shortcutFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
import Theorems.Thm_FirstPassageLinearTransport_tendsto_natLogTwo_atTop
import Theorems.Thm_FirstPassageLinearTransport_timeSupportCriticalExponent_pos
import Theorems.Thm_FirstPassageLinearTransport_timeoutStrengthenedEndpointNaturalDensityDescentWithFirstPassage
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
    {U R : ℕ → ℝ}
    (hUpos : ∀ n, 0 < U n) (hRpos : ∀ n, 0 < R n)
    (hU : Tendsto U atTop atTop) (hR : Tendsto R atTop atTop) :
    ∃ S : Set ℕ, ∃ K : ℝ,
      0 < K ∧ NaturalDensityOne S ∧
      (∀ᶠ n : ℕ in atTop, n ∈ S →
        ∃ k ell : ℕ,
          |driftGap * (k : ℝ) - (Nat.log 2 n : ℝ)| ≤
            K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          |(2 * driftGap / 3) * (ell : ℝ) - (Nat.log 2 n : ℝ)| ≤
            K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          (∀ j : ℕ, j ≤ k →
            |shortcutLogDeviation n j| ≤
              K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
          (∀ j : ℕ, j ≤ k →
            |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤
              K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
          (∀ i : ℕ, i ≤ ell →
            |rawLogDeviation n i| ≤
              K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
          ell = rawTime n k ∧
          rawOrbit ell n = orbit k n ∧
          (orbit k n : ℝ) <
            (Real.log n) ^ timeSupportCriticalExponent * U n ∧
          (∀ j : ℕ, j ≤ k →
            (orbit j n : ℝ) ≤ (n : ℝ) * R n) ∧
          (∀ i : ℕ, i ≤ ell →
            (rawOrbit i n : ℝ) ≤ (n : ℝ) * R n) ∧
          (∀ z : ℝ, (orbit k n : ℝ) ≤ z → z ≤ (n : ℝ) →
            |(shortcutFirstPassageTime n z : ℝ) -
                fixedPolylogClockCritical * Real.log ((n : ℝ) / z)| +
              |(rawFirstPassageTime n z : ℝ) -
                (3 / 2) * fixedPolylogClockCritical *
                  Real.log ((n : ℝ) / z)| ≤
                K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                  Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
            rawOrbit (rawFirstPassageTime n z) n =
              orbit (shortcutFirstPassageTime n z) n)) := by
  let Aseq := criticalMultiplierExponent U
  let Rsh := clippedShellHeight R
  let Amax := timeSupportCriticalExponent + 2
  let c := fixedPolylogClockCritical + 1
  let beta : ℝ := 1
  have hAmax : 0 < Amax := by
    dsimp [Amax]
    linarith [timeSupportCriticalExponent_pos]
  have hc : fixedPolylogClockCritical < c := by dsimp [c]; linarith
  have hbeta : 0 < beta := by dsimp [beta]; norm_num
  have hbuffer : Tendsto (sharpMovingRankBuffer Aseq) atTop atTop := by
    simpa [Aseq] using
      tendsto_sharpMovingRankBuffer_criticalMultiplierExponent hUpos hU
  have hUpper : ∀ᶠ M : ℕ in atTop, Aseq M ≤ Amax := by
    have h := eventually_criticalMultiplierExponent_le hU
    filter_upwards [h] with M hM
    exact hM.le
  have hRsh : Tendsto Rsh atTop atTop := by
    simpa [Rsh] using tendsto_clippedShellHeight_atTop hR
  obtain ⟨S, C, _eps, hC, _heps, hDense, _hShell, hWitness⟩ :=
    timeoutStrengthenedEndpointNaturalDensityDescentWithFirstPassage
      hAmax hc hbeta hbuffer hUpper hRsh
  let D := C * fixedPolylogTargetConstant timeSupportCriticalExponent
  have hTargetConstant :
      0 < fixedPolylogTargetConstant timeSupportCriticalExponent := by
    unfold fixedPolylogTargetConstant
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hw1 : ∀ᶠ M : ℕ in atTop,
      1 ≤ clippedCriticalMultiplier U M :=
    (tendsto_atTop.1 (tendsto_clippedCriticalMultiplier_atTop hU)) 1
  have hsqrtD : ∀ᶠ M : ℕ in atTop,
      D ≤ Real.sqrt (dyadicShellMinimum U M) :=
    (tendsto_atTop.1 (tendsto_sqrt_dyadicShellMinimum_atTop hU)) D
  have hScalar : ∀ᶠ M : ℕ in atTop,
      1 ≤ M ∧ 1 ≤ clippedCriticalMultiplier U M ∧
        D ≤ Real.sqrt (dyadicShellMinimum U M) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ), hw1, hsqrtD]
      with M hM hw hsqrt
    exact ⟨hM, hw, hsqrt⟩
  have hScalarAtLog := tendsto_natLogTwo_atTop.eventually hScalar
  have hFinal : ∀ᶠ n : ℕ in atTop, n ∈ S →
      ∃ k ell : ℕ,
        |driftGap * (k : ℝ) - (Nat.log 2 n : ℝ)| ≤
          C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
            Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
        |(2 * driftGap / 3) * (ell : ℝ) - (Nat.log 2 n : ℝ)| ≤
          C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
            Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
        (∀ j : ℕ, j ≤ k →
          |shortcutLogDeviation n j| ≤
            C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
        (∀ j : ℕ, j ≤ k →
          |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤
            C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
        (∀ i : ℕ, i ≤ ell →
          |rawLogDeviation n i| ≤
            C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
        ell = rawTime n k ∧
        rawOrbit ell n = orbit k n ∧
        (orbit k n : ℝ) <
          (Real.log n) ^ timeSupportCriticalExponent * U n ∧
        (∀ j : ℕ, j ≤ k →
          (orbit j n : ℝ) ≤ (n : ℝ) * R n) ∧
        (∀ i : ℕ, i ≤ ell →
        (rawOrbit i n : ℝ) ≤ (n : ℝ) * R n) ∧
        (∀ z : ℝ, (orbit k n : ℝ) ≤ z → z ≤ (n : ℝ) →
          |(shortcutFirstPassageTime n z : ℝ) -
              fixedPolylogClockCritical * Real.log ((n : ℝ) / z)| +
            |(rawFirstPassageTime n z : ℝ) -
              (3 / 2) * fixedPolylogClockCritical *
                Real.log ((n : ℝ) / z)| ≤
              C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          rawOrbit (rawFirstPassageTime n z) n =
            orbit (shortcutFirstPassageTime n z) n) := by
    filter_upwards [hWitness, hScalarAtLog,
        eventually_ge_atTop (8 : ℕ)] with n hWitness hScalar hn8
    intro hnS
    obtain ⟨k, ell, _hkBudget, hkCentered, hellCentered, hshortcutTube,
        hoddTube, hrawTube, hell, hlandingEq, hlanding, hshortcut, hraw,
        hactual⟩ := hWitness hnS
    let M := Nat.log 2 n
    have hnpos : 0 < n := by omega
    have hnShell : n ∈ dyadicShell M := mem_dyadicShell_log hnpos
    obtain ⟨hM, hw, hsqrt⟩ := hScalar
    have hlogn : 1 ≤ Real.log n := by
      have hlog8 : 1 ≤ Real.log (8 : ℝ) := by
        rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
        have hlog2Half : (1 / 2 : ℝ) < Real.log 2 :=
          (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
            Real.log_two_gt_d9
        norm_num only [Nat.cast_ofNat]
        nlinarith
      exact hlog8.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hn8))
    have hlogpow0 : 0 ≤
        (Real.log n) ^ timeSupportCriticalExponent := by positivity
    have hAseqScale := shellLog_rpow_criticalMultiplierExponent_le
      U hM hnShell
    have hTerminal := two_pow_criticalMultiplierTerminalRank_lt hUpos hw
    have hShellTarget := shellPolylogTarget_le_natLog
      timeSupportCriticalExponent_pos.le hnShell hlogn
    have hw0 : 0 ≤ clippedCriticalMultiplier U M :=
      (clippedCriticalMultiplier_pos hUpos M).le
    have hScaledShellTarget :
        2 * (((M : ℝ) + 2) ^ timeSupportCriticalExponent) *
            clippedCriticalMultiplier U M ≤
          fixedPolylogTargetConstant timeSupportCriticalExponent *
            (Real.log n) ^ timeSupportCriticalExponent *
              clippedCriticalMultiplier U M := by
      exact mul_le_mul_of_nonneg_right hShellTarget hw0
    have hMin0 : 0 ≤ dyadicShellMinimum U M :=
      (dyadicShellMinimum_pos hUpos M).le
    have hsqrt0 : 0 ≤ Real.sqrt (dyadicShellMinimum U M) :=
      Real.sqrt_nonneg _
    have hDw : D * clippedCriticalMultiplier U M ≤ U n := by
      have hwle := clippedCriticalMultiplier_le_sqrt U M
      have h₁ : D * clippedCriticalMultiplier U M ≤
          D * Real.sqrt (dyadicShellMinimum U M) :=
        mul_le_mul_of_nonneg_left hwle hD.le
      have h₂ : D * Real.sqrt (dyadicShellMinimum U M) ≤
          Real.sqrt (dyadicShellMinimum U M) *
            Real.sqrt (dyadicShellMinimum U M) :=
        mul_le_mul_of_nonneg_right hsqrt hsqrt0
      have h₃ : Real.sqrt (dyadicShellMinimum U M) *
          Real.sqrt (dyadicShellMinimum U M) =
            dyadicShellMinimum U M := by
        nlinarith [Real.sq_sqrt hMin0]
      exact h₁.trans (h₂.trans_eq h₃) |>.trans
        (dyadicShellMinimum_le_of_mem U hnShell)
    have hTarget : (orbit k n : ℝ) <
        (Real.log n) ^ timeSupportCriticalExponent * U n := by
      calc
        (orbit k n : ℝ) < C * (Real.log n) ^ (Aseq M) := by
          simpa [Aseq, M] using hlanding
        _ ≤ C * (2 : ℝ) ^ (criticalMultiplierTerminalRank U M) :=
          mul_le_mul_of_nonneg_left hAseqScale hC.le
        _ < C * (2 * (((M : ℝ) + 2) ^ timeSupportCriticalExponent) *
            clippedCriticalMultiplier U M) :=
          mul_lt_mul_of_pos_left hTerminal hC
        _ ≤ C * (fixedPolylogTargetConstant timeSupportCriticalExponent *
            (Real.log n) ^ timeSupportCriticalExponent *
              clippedCriticalMultiplier U M) :=
          mul_le_mul_of_nonneg_left hScaledShellTarget hC.le
        _ = (Real.log n) ^ timeSupportCriticalExponent *
            (D * clippedCriticalMultiplier U M) := by
          dsimp [D]
          ring
        _ ≤ (Real.log n) ^ timeSupportCriticalExponent * U n :=
          mul_le_mul_of_nonneg_left hDw hlogpow0
    have hRshLe : Rsh M ≤ R n := by
      simpa [Rsh] using clippedShellHeight_le_of_mem R hnShell
    have hRsh0 : 0 ≤ Rsh M := by
      simpa [Rsh] using (clippedShellHeight_pos hRpos M).le
    refine ⟨k, ell, hkCentered, hellCentered, hshortcutTube, hoddTube,
      hrawTube, hell, hlandingEq, hTarget, ?_, ?_, hactual⟩
    · intro j hj
      have hjBound := hshortcut j hj
      have hhalf : (n : ℝ) * Rsh M / 2 ≤ (n : ℝ) * Rsh M := by
        have hn0 : (0 : ℝ) ≤ n := by positivity
        nlinarith [mul_nonneg hn0 hRsh0]
      exact hjBound.trans (hhalf.trans
        (mul_le_mul_of_nonneg_left hRshLe (by positivity)))
    · intro i hi
      exact (hraw i hi).trans
        (mul_le_mul_of_nonneg_left hRshLe (by positivity))
  exact ⟨S, C, hC, hDense, hFinal⟩
end FirstPassageLinearTransport
