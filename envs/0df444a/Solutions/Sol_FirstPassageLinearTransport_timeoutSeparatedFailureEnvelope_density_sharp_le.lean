-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutSeparatedFailureEnvelope_density_sharp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:23:19.996638+00:00
-- url     : https://prove2.me/submissions/925dd38a-5255-4720-bef6-1910e63dff84

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
import Theorems.Thm_FirstPassageLinearTransport_timeoutHighFirstBadSourcesAtRank_density_le
import Theorems.Thm_FirstPassageLinearTransport_timeoutSeparatedFailureEnvelope_card_le
import Theorems.Thm_FirstPassageLinearTransport_timeout_low_firstBad_sharp_sum_canonical_le
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
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {M L S : ℕ} {H dHi C b₀ b : ℝ}
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hM : 1 ≤ M) (hLS : L + 1 ≤ S) (hSM : S < M) (hL : 2 ≤ L)
    (hH0 : 0 ≤ H) (hC : 0 ≤ C)
    (hnextPos : ∀ p ∈ Finset.Icc (L + 1) S,
      0 < timeoutTargetRank K₀ L (p - 1))
    (hnextLt : ∀ p ∈ Finset.Icc (L + 1) S,
      timeoutTargetRank K₀ L (p - 1) < p)
    (hsmall : ∀ q ∈ Finset.Icc L (M - 1),
      ((((q + 2 : ℕ) : ℚ) / rStar) /
        ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3)
    (hTimes : ∀ q ∈ Finset.Icc L (M - 1),
      ((timeoutFeasibleTimes P K₀ L M S q).card : ℝ) ≤ H)
    (hInitial :
      ((shellInitialWindowBad M (timeoutHighTolerance P M M)).card : ℝ) /
        (2 : ℝ) ^ M ≤ dHi)
    (hHigh : ∀ q ∈ Finset.Icc (S + 1) (M - 1),
      ((landingBad q (timeoutHighTolerance P M (q - 1))).card : ℝ) /
        (2 : ℝ) ^ q ≤ dHi)
    (hLow : ∀ p ∈ Finset.Icc (L + 1) S,
      ((timeoutLandingBad K₀ L p).card : ℝ) / (2 : ℝ) ^ p ≤
        (C / Real.sqrt ((p - 1 : ℕ) : ℝ)) *
          Real.exp (-(b * ((p - 1 : ℕ) : ℝ))))
    (hb₀ : 0 < b₀) (hb₀b : b₀ ≤ b) :
    ((timeoutSeparatedFailureEnvelope P K₀ M L S).card : ℝ) /
        (2 : ℝ) ^ M ≤
      dHi + H * (1 + 6 / (rStar : ℝ)) * ((M : ℝ) + 1) ^ 2 * dHi +
        H * (1 + 6 / (rStar : ℝ)) *
          exactSharpCriticalLowSeriesConstant b₀ C *
            (Real.sqrt (L + 1) * Real.exp (-(b * (L : ℝ)))) := by
  have hLowSum := timeout_low_firstBad_sharp_sum_canonical_le
    hrStar hStarHi hStarLo hM hLS hSM hL hnextPos hnextLt
    (fun p hp =>
      have hpi := Finset.mem_Icc.mp hp
      hsmall p (Finset.mem_Icc.mpr
        ⟨(Nat.le_succ L).trans hpi.1,
          hpi.2.trans (Nat.le_pred_of_lt hSM)⟩))
    (fun p hp =>
      have hpi := Finset.mem_Icc.mp hp
      hTimes p (Finset.mem_Icc.mpr
        ⟨(Nat.le_succ L).trans hpi.1,
          hpi.2.trans (Nat.le_pred_of_lt hSM)⟩))
    hLow hC hb₀ hb₀b
  have hcardNat := timeoutSeparatedFailureEnvelope_card_le P K₀ M L S
  have hcard :
      ((timeoutSeparatedFailureEnvelope P K₀ M L S).card : ℝ) ≤
        ((shellInitialWindowBad M (timeoutHighTolerance P M M)).card : ℝ) +
        ∑ q ∈ Finset.Icc (S + 1) (M - 1),
          ((timeoutHighFirstBadSourcesAtRank P K₀ L M S q).card : ℝ) +
        ∑ p ∈ Finset.Icc (L + 1) S,
          ((timeoutFirstBadSourcesAtRank P K₀ L M S p).card : ℝ) := by
    exact_mod_cast hcardNat
  have hpowM : 0 < (2 : ℝ) ^ M := by positivity
  have hHighEach : ∀ q ∈ Finset.Icc (S + 1) (M - 1),
      ((timeoutHighFirstBadSourcesAtRank P K₀ L M S q).card : ℝ) /
          (2 : ℝ) ^ M ≤
        H * (1 + 6 / (rStar : ℝ)) * ((q + 1 : ℕ) : ℝ) * dHi := by
    intro q hq
    have hqi := Finset.mem_Icc.mp hq
    have hqAll : q ∈ Finset.Icc L (M - 1) :=
      Finset.mem_Icc.mpr
        ⟨(Nat.le_succ L).trans
            (hLS.trans ((Nat.le_succ S).trans hqi.1)), hqi.2⟩
    have hqM : q < M := Nat.lt_of_le_pred (by omega) hqi.2
    apply timeoutHighFirstBadSourcesAtRank_density_le
      hrStar hStarHi hStarLo hM hqM (hsmall q hqAll)
      (hTimes q hqAll)
    simpa [timeoutHighTargetTolerance] using hHigh q hq
  have hdHi0 : 0 ≤ dHi := by
    have hnonneg : 0 ≤
        ((shellInitialWindowBad M (timeoutHighTolerance P M M)).card : ℝ) /
          (2 : ℝ) ^ M := by positivity
    linarith
  have hHighSum :
      ∑ q ∈ Finset.Icc (S + 1) (M - 1),
          ((timeoutHighFirstBadSourcesAtRank P K₀ L M S q).card : ℝ) /
            (2 : ℝ) ^ M ≤
        H * (1 + 6 / (rStar : ℝ)) * ((M : ℝ) + 1) ^ 2 * dHi := by
    calc
      _ ≤ ∑ _q ∈ Finset.Icc (S + 1) (M - 1),
          H * (1 + 6 / (rStar : ℝ)) * ((M : ℝ) + 1) * dHi := by
        apply Finset.sum_le_sum
        intro q hq
        have hqi := Finset.mem_Icc.mp hq
        have hq1 : ((q + 1 : ℕ) : ℝ) ≤ (M : ℝ) + 1 := by
          exact_mod_cast (show q + 1 ≤ M + 1 by omega)
        exact (hHighEach q hq).trans (by
          have hcoef0 : 0 ≤ H * (1 + 6 / (rStar : ℝ)) := by
            have hrR : (0 : ℝ) < (rStar : ℝ) := by exact_mod_cast hrStar
            positivity
          gcongr)
      _ ≤ H * (1 + 6 / (rStar : ℝ)) * ((M : ℝ) + 1) ^ 2 * dHi := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcardI : ((Finset.Icc (S + 1) (M - 1)).card : ℝ) ≤
            (M : ℝ) + 1 := by
          rw [Nat.card_Icc]
          exact_mod_cast (show M - 1 + 1 - (S + 1) ≤ M + 1 by omega)
        have hrR : (0 : ℝ) < (rStar : ℝ) := by exact_mod_cast hrStar
        have hcoef0 : 0 ≤ H * (1 + 6 / (rStar : ℝ)) *
            ((M : ℝ) + 1) * dHi := by positivity
        calc
          ((Finset.Icc (S + 1) (M - 1)).card : ℝ) *
              (H * (1 + 6 / (rStar : ℝ)) * ((M : ℝ) + 1) * dHi) ≤
            ((M : ℝ) + 1) *
              (H * (1 + 6 / (rStar : ℝ)) * ((M : ℝ) + 1) * dHi) :=
            mul_le_mul_of_nonneg_right hcardI hcoef0
          _ = _ := by ring
  have hdiv :
      ((timeoutSeparatedFailureEnvelope P K₀ M L S).card : ℝ) /
          (2 : ℝ) ^ M ≤
        ((shellInitialWindowBad M (timeoutHighTolerance P M M)).card : ℝ) /
            (2 : ℝ) ^ M +
        ∑ q ∈ Finset.Icc (S + 1) (M - 1),
          ((timeoutHighFirstBadSourcesAtRank P K₀ L M S q).card : ℝ) /
            (2 : ℝ) ^ M +
        ∑ p ∈ Finset.Icc (L + 1) S,
          ((timeoutFirstBadSourcesAtRank P K₀ L M S p).card : ℝ) /
            (2 : ℝ) ^ M := by
    have h := div_le_div_of_nonneg_right hcard hpowM.le
    simpa [add_div, Finset.sum_div] using h
  exact hdiv.trans (add_le_add (add_le_add hInitial hHighSum) hLowSum)
end FirstPassageLinearTransport
