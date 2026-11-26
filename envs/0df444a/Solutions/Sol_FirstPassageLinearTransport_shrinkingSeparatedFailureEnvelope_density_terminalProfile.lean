-- Prove2me | solution 1 for FirstPassageLinearTransport.shrinkingSeparatedFailureEnvelope_density_terminalProfile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:00:52.334925+00:00
-- url     : https://prove2.me/submissions/9d4dded0-0826-44b4-805e-7907dac13f3f

import Definitions.Def_FirstPassageLinearTransport_ShrinkingFirstBad
import Definitions.Def_FirstPassageLinearTransport_ShrinkingProfile
import Theorems.Thm_FirstPassageLinearTransport_shrinkingTargetTolerance_eq_high
import Theorems.Thm_FirstPassageLinearTransport_shrinkingTargetTolerance_eq_low
import Theorems.Thm_FirstPassageLinearTransport_shrinkingSeparatedFailureEnvelope_card_le
import Theorems.Thm_FirstPassageLinearTransport_shrinkingFirstBadSourcesAtRank_density_le
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_landingBad_density_le
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
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_terminal_rank_sum_le
attribute [local simp] FirstPassageLinearTransport.StageSetup.lowerTolerance_M0
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
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
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.shrinkingHighSetup_M0



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : ShrinkingBarrierRunData)
    {M L S : ℕ} {H dHi bLo bLo' c' : ℝ}
    (hLS : L ≤ S) (hSM : S < M) (hL1 : 1 ≤ L)
    (hH0 : 0 ≤ H)
    (hsmall : ∀ q ∈ Finset.Icc L (M - 1),
      ((((q + 2 : ℕ) : ℚ) / P.rStar) /
        ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3)
    (hTimes : ∀ q ∈ Finset.Icc L (M - 1),
      ((shrinkingFeasibleTimes P M S q).card : ℝ) ≤ H)
    (hInitial :
      ((shellInitialWindowBad M (shrinkingHighTolerance P M M)).card : ℝ) /
        (2 : ℝ) ^ M ≤ dHi)
    (hHigh : ∀ q ∈ Finset.Icc (S + 1) (M - 1),
      ((landingBad q (shrinkingHighTolerance P M (q - 1))).card : ℝ) /
        (2 : ℝ) ^ q ≤ dHi)
    (hLow : ∀ q ∈ Finset.Icc L S,
      ((landingBad q P.etaLo).card : ℝ) ≤
        1 + (2 : ℝ) ^ q * Real.exp (-(((q - 1 : ℕ) : ℝ) * bLo)))
    (hbLo' : 0 < bLo') (hLoRate : bLo' < bLo)
    (hc' : 0 < c') (hc2 : c' < Real.log 2) :
    ((shrinkingSeparatedFailureEnvelope P M L S).card : ℝ) /
        (2 : ℝ) ^ M ≤
      dHi + H * (1 + 6 / (P.rStar : ℝ)) *
        (((M : ℝ) + 1) ^ 2 * dHi + terminalTailBound bLo bLo' c' L) := by
  have hcardNat := shrinkingSeparatedFailureEnvelope_card_le P M L S
  have hcard :
      ((shrinkingSeparatedFailureEnvelope P M L S).card : ℝ) ≤
        ((shellInitialWindowBad M (shrinkingHighTolerance P M M)).card : ℝ) +
        ∑ q ∈ Finset.Icc (S + 1) (M - 1),
          ((shrinkingFirstBadSourcesAtRank P M S q).card : ℝ) +
        ∑ q ∈ Finset.Icc L S,
          ((shrinkingFirstBadSourcesAtRank P M S q).card : ℝ) := by
    exact_mod_cast hcardNat
  have hpowM : 0 < (2 : ℝ) ^ M := by positivity
  have hHighEach : ∀ q ∈ Finset.Icc (S + 1) (M - 1),
      ((shrinkingFirstBadSourcesAtRank P M S q).card : ℝ) /
          (2 : ℝ) ^ M ≤
        H * (1 + 6 / (P.rStar : ℝ)) * ((q + 1 : ℕ) : ℝ) * dHi := by
    intro q hq
    have hqAll : q ∈ Finset.Icc L (M - 1) := by
      have hqi := Finset.mem_Icc.mp hq
      exact Finset.mem_Icc.mpr ⟨hLS.trans (by omega), hqi.2⟩
    apply shrinkingFirstBadSourcesAtRank_density_le P
      (by have := (Finset.mem_Icc.mp hqAll).2; omega) (hsmall q hqAll)
      (hTimes q hqAll)
    rw [shrinkingTargetTolerance_eq_high P (Finset.mem_Icc.mp hq).1]
    exact hHigh q hq
  have hLowEach : ∀ q ∈ Finset.Icc L S,
      ((shrinkingFirstBadSourcesAtRank P M S q).card : ℝ) /
          (2 : ℝ) ^ M ≤
        H * (1 + 6 / (P.rStar : ℝ)) * ((q + 1 : ℕ) : ℝ) *
          (Real.exp (-(Real.log 2 * (q : ℝ))) +
            Real.exp bLo * Real.exp (-(bLo * (q : ℝ)))) := by
    intro q hq
    have hqi := Finset.mem_Icc.mp hq
    have hqAll : q ∈ Finset.Icc L (M - 1) := by
      exact Finset.mem_Icc.mpr ⟨hqi.1, by omega⟩
    apply shrinkingFirstBadSourcesAtRank_density_le P
      (by omega) (hsmall q hqAll)
      (hTimes q hqAll)
    rw [shrinkingTargetTolerance_eq_low P (hL1.trans hqi.1) hqi.2]
    exact landingBad_density_le (hL1.trans hqi.1) (hLow q hq)
  have hHighSum :
      ∑ q ∈ Finset.Icc (S + 1) (M - 1),
          ((shrinkingFirstBadSourcesAtRank P M S q).card : ℝ) /
            (2 : ℝ) ^ M ≤
        H * (1 + 6 / (P.rStar : ℝ)) * ((M : ℝ) + 1) ^ 2 * dHi := by
    have hdHi0 : 0 ≤ dHi := by
      have hnonneg : 0 ≤
          ((shellInitialWindowBad M (shrinkingHighTolerance P M M)).card : ℝ) /
            (2 : ℝ) ^ M := by positivity
      linarith
    calc
      _ ≤ ∑ _q ∈ Finset.Icc (S + 1) (M - 1),
          H * (1 + 6 / (P.rStar : ℝ)) * ((M : ℝ) + 1) * dHi := by
        apply Finset.sum_le_sum
        intro q hq
        have hqM := (Finset.mem_Icc.mp hq).2
        have hq1 : ((q + 1 : ℕ) : ℝ) ≤ (M : ℝ) + 1 := by
          exact_mod_cast (by omega : q + 1 ≤ M + 1)
        have hbase := hHighEach q hq
        have hnonneg : 0 ≤ H * (1 + 6 / (P.rStar : ℝ)) := by
          have hrR : (0 : ℝ) < (P.rStar : ℝ) := by exact_mod_cast P.rStar_pos
          positivity
        exact hbase.trans (by gcongr)
      _ ≤ H * (1 + 6 / (P.rStar : ℝ)) * ((M : ℝ) + 1) ^ 2 * dHi := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcard : ((Finset.Icc (S + 1) (M - 1)).card : ℝ) ≤
            (M : ℝ) + 1 := by
          rw [Nat.card_Icc]
          exact_mod_cast (by omega : M - 1 + 1 - (S + 1) ≤ M + 1)
        have hcoef0 : 0 ≤ H * (1 + 6 / (P.rStar : ℝ)) *
            ((M : ℝ) + 1) * dHi := by
          have hrR : (0 : ℝ) < (P.rStar : ℝ) := by exact_mod_cast P.rStar_pos
          positivity
        calc
          ((Finset.Icc (S + 1) (M - 1)).card : ℝ) *
              (H * (1 + 6 / (P.rStar : ℝ)) * ((M : ℝ) + 1) * dHi) ≤
            ((M : ℝ) + 1) *
              (H * (1 + 6 / (P.rStar : ℝ)) * ((M : ℝ) + 1) * dHi) :=
            mul_le_mul_of_nonneg_right hcard hcoef0
          _ = _ := by ring
  have hLowSum :
      ∑ q ∈ Finset.Icc L S,
          ((shrinkingFirstBadSourcesAtRank P M S q).card : ℝ) /
            (2 : ℝ) ^ M ≤
        H * (1 + 6 / (P.rStar : ℝ)) * terminalTailBound bLo bLo' c' L := by
    calc
      _ ≤ ∑ q ∈ Finset.Icc L S,
          H * (1 + 6 / (P.rStar : ℝ)) * ((q + 1 : ℕ) : ℝ) *
            (Real.exp (-(Real.log 2 * (q : ℝ))) +
              Real.exp bLo * Real.exp (-(bLo * (q : ℝ)))) := by
        exact Finset.sum_le_sum hLowEach
      _ = H * (1 + 6 / (P.rStar : ℝ)) *
          (∑ q ∈ Finset.Icc L S, ((q + 1 : ℕ) : ℝ) *
            (Real.exp (-(Real.log 2 * (q : ℝ))) +
              Real.exp bLo * Real.exp (-(bLo * (q : ℝ))))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ ≤ H * (1 + 6 / (P.rStar : ℝ)) * terminalTailBound bLo bLo' c' L := by
        have htail := terminal_rank_sum_le hbLo' hLoRate hc' hc2 L S
        have hcoef0 : 0 ≤ H * (1 + 6 / (P.rStar : ℝ)) := by
          have hrR : (0 : ℝ) < (P.rStar : ℝ) := by exact_mod_cast P.rStar_pos
          positivity
        exact mul_le_mul_of_nonneg_left htail hcoef0
  have hdiv :
      ((shrinkingSeparatedFailureEnvelope P M L S).card : ℝ) /
          (2 : ℝ) ^ M ≤
        ((shellInitialWindowBad M (shrinkingHighTolerance P M M)).card : ℝ) /
            (2 : ℝ) ^ M +
          ∑ q ∈ Finset.Icc (S + 1) (M - 1),
            ((shrinkingFirstBadSourcesAtRank P M S q).card : ℝ) /
              (2 : ℝ) ^ M +
          ∑ q ∈ Finset.Icc L S,
            ((shrinkingFirstBadSourcesAtRank P M S q).card : ℝ) /
              (2 : ℝ) ^ M := by
    have := div_le_div_of_nonneg_right hcard hpowM.le
    simpa [add_div, Finset.sum_div] using this
  calc
    _ ≤ ((shellInitialWindowBad M (shrinkingHighTolerance P M M)).card : ℝ) /
            (2 : ℝ) ^ M +
          ∑ q ∈ Finset.Icc (S + 1) (M - 1),
            ((shrinkingFirstBadSourcesAtRank P M S q).card : ℝ) /
              (2 : ℝ) ^ M +
          ∑ q ∈ Finset.Icc L S,
            ((shrinkingFirstBadSourcesAtRank P M S q).card : ℝ) /
              (2 : ℝ) ^ M := hdiv
    _ ≤ dHi +
        H * (1 + 6 / (P.rStar : ℝ)) * ((M : ℝ) + 1) ^ 2 * dHi +
        H * (1 + 6 / (P.rStar : ℝ)) * terminalTailBound bLo bLo' c' L :=
      add_le_add (add_le_add hInitial hHighSum) hLowSum
    _ = dHi + H * (1 + 6 / (P.rStar : ℝ)) *
        (((M : ℝ) + 1) ^ 2 * dHi + terminalTailBound bLo bLo' c' L) := by ring
end FirstPassageLinearTransport
