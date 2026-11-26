-- Prove2me | solution 1 for FirstPassageLinearTransport.collatzSurvivalMass_le_fullWordBins
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:07:23.300856+00:00
-- url     : https://prove2.me/submissions/937678c4-11c4-4aa4-bcea-df72fab85cbf

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Theorems.Thm_FirstPassageLinearTransport_wordSurvivesFrom_terminal
import Theorems.Thm_FirstPassageLinearTransport_collatzFullBarrierBinEvent_at_index
import Theorems.Thm_FirstPassageLinearTransport_collatzTerminalBinIndex_lt
import Theorems.Thm_FirstPassageLinearTransport_collatzFullBarrierBinIndicator_nonneg
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_bernoulliWordWeight_nonneg
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_scale
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.card_boolSupport_cons
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.stoppedBallotValue_cons



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {m Q : ℕ} {B : ℝ}
    (hQ : m + ⌈B⌉₊ + 2 ≤ Q) :
    weightedSurvivalWordMass (1 / 2) collatzLogIncrement (-B) m 0 ≤
      ∑ q ∈ Finset.range Q,
        collatzFullWordMass (1 / 2) m B (q : ℝ) := by
  classical
  unfold weightedSurvivalWordMass collatzFullWordMass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro v _hv
  by_cases hsurv : wordSurvivesFrom (-B) collatzLogIncrement m 0 v
  · have hterminal := wordSurvivesFrom_terminal hsurv
    have hnonneg : 0 ≤ B + wordIncrementSum collatzLogIncrement v := by
      linarith
    have hindex := collatzTerminalBinIndex_lt hnonneg
    have hindexQ : collatzTerminalBinIndex B v ∈ Finset.range Q := by
      simp only [Finset.mem_range]
      omega
    have hevent := collatzFullBarrierBinEvent_at_index hsurv
    calc
      bernoulliWordWeight (1 / 2) v *
          (if wordSurvivesFrom (-B) collatzLogIncrement m 0 v then 1 else 0) =
          bernoulliWordWeight (1 / 2) v *
            collatzFullBarrierBinIndicator B (collatzTerminalBinIndex B v) v := by
        simp [hsurv, collatzFullBarrierBinIndicator, hevent]
      _ ≤ ∑ q ∈ Finset.range Q,
          bernoulliWordWeight (1 / 2) v *
            collatzFullBarrierBinIndicator B (q : ℝ) v := by
        exact Finset.single_le_sum
          (f := fun q : ℕ => bernoulliWordWeight (1 / 2) v *
            collatzFullBarrierBinIndicator B (q : ℝ) v)
          (fun q _hq => mul_nonneg
            (bernoulliWordWeight_nonneg (by norm_num) (by norm_num) v)
            (collatzFullBarrierBinIndicator_nonneg B (q : ℝ) v))
          hindexQ
  · simp only [hsurv, if_false, mul_zero]
    exact Finset.sum_nonneg fun q _hq =>
      mul_nonneg
        (bernoulliWordWeight_nonneg (by norm_num) (by norm_num) v)
        (collatzFullBarrierBinIndicator_nonneg B (q : ℝ) v)
end FirstPassageLinearTransport
