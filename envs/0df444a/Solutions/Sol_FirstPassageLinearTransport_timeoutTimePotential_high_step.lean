-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutTimePotential_high_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:11:30.805967+00:00
-- url     : https://prove2.me/submissions/ea20c600-d55b-4bac-a16f-0de33ce2a499

import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
import Theorems.Thm_FirstPassageLinearTransport_timeoutDurationError_high_le
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
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_firstBadLandingEnvelope
import Theorems.Thm_FirstPassageLinearTransport_mem_generatedFirstBadSources
import Theorems.Thm_FirstPassageLinearTransport_mem_landingBad
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSourcesAtTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFeasibleTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
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
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
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


section
namespace FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
private theorem timeout_sqrt_rat_lt_one
    {r : ℚ} (hr1 : r < 1) :
    Real.sqrt (r : ℝ) < 1 := by
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
  norm_num
  exact_mod_cast hr1
end
end FirstPassageLinearTransport
end

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : TimeoutHighRunData) {M S m q : ℕ}
    (hM : 1 ≤ M) (hm : 1 ≤ m) (hSm : S ≤ m)
    (hq : (q : ℝ) ≤ (P.rHi : ℝ) * (m : ℝ)) :
    timeoutDurationError (timeoutHighTolerance P M m) m +
        timeoutTimePotential P M S q ≤
      timeoutTimePotential P M S (m + 1) := by
  have hrHi0 : (0 : ℝ) ≤ P.rHi := P.pHi.r_pos.le
  have hsHi1 := timeout_sqrt_rat_lt_one
    (by exact_mod_cast P.pHi.r_lt_one : P.rHi < 1)
  have hdHi : 0 < 1 - Real.sqrt (P.rHi : ℝ) := sub_pos.mpr hsHi1
  have hcoefHi : 0 < P.D + P.tau + 3 := by
    nlinarith [P.D_pos, P.pHi.eta_pos]
  have hlog0 : 0 ≤ Real.sqrt (Real.log ((M : ℝ) + 2)) := Real.sqrt_nonneg _
  have hcost := timeoutDurationError_high_le P hM hm
  have hprevHigh : S < m + 1 := by omega
  by_cases hqHigh : S < q
  · have hsqrtq : Real.sqrt (q : ℝ) ≤
        Real.sqrt (P.rHi : ℝ) * Real.sqrt (m : ℝ) := by
      have hs := Real.sqrt_le_sqrt hq
      rw [Real.sqrt_mul hrHi0] at hs
      exact hs
    have hmSucc : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by norm_num
    have hsqrtm : Real.sqrt (m : ℝ) ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt hmSucc
    simp only [timeoutTimePotential, if_pos hqHigh, if_pos hprevHigh]
    have hscaled :
        (P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
              Real.sqrt (m : ℝ) +
            ((P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
              Real.sqrt (q : ℝ)) / (1 - Real.sqrt (P.rHi : ℝ)) ≤
          ((P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
            Real.sqrt ((m + 1 : ℕ) : ℝ)) /
              (1 - Real.sqrt (P.rHi : ℝ)) := by
      apply (le_div_iff₀ hdHi).2
      rw [add_mul, div_mul_cancel₀ _ hdHi.ne']
      have hmulq := mul_le_mul_of_nonneg_left hsqrtq
        (mul_nonneg hcoefHi.le hlog0)
      have hmulm := mul_le_mul_of_nonneg_left hsqrtm
        (mul_nonneg hcoefHi.le hlog0)
      nlinarith
    linarith
  · have hqLow : q ≤ S := by omega
    simp only [timeoutTimePotential, if_neg hqHigh, if_pos hprevHigh]
    have hlowReserve : (S : ℝ) * (q : ℝ) ≤ (S : ℝ) ^ 2 := by
      have hqR : (q : ℝ) ≤ S := by exact_mod_cast hqLow
      have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
      nlinarith
    have hmSucc : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by norm_num
    have hsqrtm : Real.sqrt (m : ℝ) ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt hmSucc
    have hhighPay :
        (P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
            Real.sqrt (m : ℝ) ≤
          ((P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
            Real.sqrt ((m + 1 : ℕ) : ℝ)) /
              (1 - Real.sqrt (P.rHi : ℝ)) := by
      have hbase := mul_le_mul_of_nonneg_left hsqrtm
        (mul_nonneg hcoefHi.le hlog0)
      have hdiv :
          (P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
              Real.sqrt ((m + 1 : ℕ) : ℝ) ≤
            ((P.D + P.tau + 3) * Real.sqrt (Real.log ((M : ℝ) + 2)) *
              Real.sqrt ((m + 1 : ℕ) : ℝ)) /
                (1 - Real.sqrt (P.rHi : ℝ)) := by
        apply (le_div_iff₀ hdHi).2
        let A := (P.D + P.tau + 3) *
          Real.sqrt (Real.log ((M : ℝ) + 2)) *
            Real.sqrt ((m + 1 : ℕ) : ℝ)
        have hA0 : 0 ≤ A := by
          dsimp [A]
          positivity
        have hdenLe : 1 - Real.sqrt (P.rHi : ℝ) ≤ 1 := by
          linarith [Real.sqrt_nonneg (P.rHi : ℝ)]
        change A * (1 - Real.sqrt (P.rHi : ℝ)) ≤ A
        calc
          A * (1 - Real.sqrt (P.rHi : ℝ)) ≤ A * 1 :=
            mul_le_mul_of_nonneg_left hdenLe hA0
          _ = A := mul_one A
      exact hbase.trans hdiv
    linarith
end FirstPassageLinearTransport
