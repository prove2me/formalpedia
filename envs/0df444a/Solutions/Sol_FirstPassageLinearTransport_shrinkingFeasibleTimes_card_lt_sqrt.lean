-- Prove2me | solution 1 for FirstPassageLinearTransport.shrinkingFeasibleTimes_card_lt_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:00:29.106422+00:00
-- url     : https://prove2.me/submissions/13cf1e73-135b-4539-a8c0-32f50348bc98

import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Theorems.Thm_FirstPassageLinearTransport_shrinkingTimePotential_source_le_sqrt
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_pos
import Theorems.Thm_FirstPassageLinearTransport_driftGap_pos
import Theorems.Thm_FirstPassageLinearTransport_shrinkingFeasibleTimes_card_le_potential


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : ShrinkingBarrierRunData) {C : ℝ} (hC : 0 ≤ C)
    {M q : ℕ} (hM : 1 ≤ M)
    (hSwitch : shrinkingSwitchRank C M < M + 1) :
    ((shrinkingFeasibleTimes P M (shrinkingSwitchRank C M) q).card : ℝ) <
      (shrinkingTimeSupportConstant P C + 1) *
        Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
  have hcard := shrinkingFeasibleTimes_card_le_potential P
    (S := shrinkingSwitchRank C M) (q := q) hM
  have hceil :
      (⌈(1 + 2 * shrinkingTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
        driftGap)⌉₊ : ℝ) <
      (1 + 2 * shrinkingTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
        driftGap) + 1 := by
    apply Nat.ceil_lt_add_one
    have hpot0 : 0 ≤ shrinkingTimePotential P M
        (shrinkingSwitchRank C M) (M + 1) := by
      have hsqrt : Real.sqrt (P.rHi : ℝ) < 1 := by
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
        norm_num
        exact_mod_cast P.pHi.r_lt_one
      have hrLo : (P.rLo : ℝ) < 1 := by exact_mod_cast P.pLo.r_lt_one
      have hcoefHi : 0 ≤ P.D + P.tau + 3 := by
        nlinarith [P.D_pos, P.pHi.eta_pos]
      have hcoefLo : 0 ≤ 2 * P.etaLo + 3 := by nlinarith [P.pLo.eta_pos]
      have hlog0 : 0 ≤ Real.log ((M : ℝ) + 2) :=
        Real.log_nonneg (by
          have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
          linarith)
      rw [shrinkingTimePotential, if_pos hSwitch]
      apply add_nonneg
      · exact div_nonneg
          (mul_nonneg (mul_nonneg hcoefHi (Real.sqrt_nonneg _))
            (Real.sqrt_nonneg _)) (sub_pos.mpr hsqrt).le
      · exact div_nonneg
          (mul_nonneg hcoefLo (Nat.cast_nonneg _)) (sub_pos.mpr hrLo).le
    have hquot : 0 ≤
        2 * shrinkingTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
          driftGap := div_nonneg (mul_nonneg (by norm_num) hpot0) driftGap_pos.le
    linarith
  have hbound := shrinkingTimePotential_source_le_sqrt P hC hM hSwitch
  have hsqrt1 : 1 ≤
      Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    have hlog1 : 1 ≤ Real.log ((M : ℝ) + 2) := by
      apply (Real.le_log_iff_exp_le (by positivity)).2
      have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
      have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
      linarith
    nlinarith
  have hcardR :
      ((shrinkingFeasibleTimes P M (shrinkingSwitchRank C M) q).card : ℝ) ≤
        (⌈(1 + 2 * shrinkingTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
          driftGap)⌉₊ : ℝ) := by exact_mod_cast hcard
  calc
    ((shrinkingFeasibleTimes P M (shrinkingSwitchRank C M) q).card : ℝ) ≤
        (⌈(1 + 2 * shrinkingTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
          driftGap)⌉₊ : ℝ) := hcardR
    _ < (1 + 2 * shrinkingTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
          driftGap) + 1 := hceil
    _ ≤ shrinkingTimeSupportConstant P C *
          Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) + 1 := by
      linarith
    _ ≤ (shrinkingTimeSupportConstant P C + 1) *
          Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
      nlinarith
end FirstPassageLinearTransport
