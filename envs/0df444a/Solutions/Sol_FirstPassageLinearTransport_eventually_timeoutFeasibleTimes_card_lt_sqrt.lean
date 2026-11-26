-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_timeoutFeasibleTimes_card_lt_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:17:15.770194+00:00
-- url     : https://prove2.me/submissions/ebaa5eb6-f793-40e5-ba4c-02c6c76ff23c

import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
import Theorems.Thm_FirstPassageLinearTransport_timeoutTimePotential_nonneg
import Theorems.Thm_FirstPassageLinearTransport_timeoutFeasibleTimes_card_le_potential
import Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutTimePotential_source_le_sqrt
import Theorems.Thm_FirstPassageLinearTransport_driftGap_pos


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : TimeoutHighRunData) (K₀ : ℝ) {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ M : ℕ in atTop,
      ∀ L q : ℕ,
        ((timeoutFeasibleTimes P K₀ L M (shrinkingSwitchRank C M) q).card : ℝ) <
          (timeoutTimeSupportConstant P C + 1) *
            Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
  filter_upwards [eventually_timeoutTimePotential_source_le_sqrt P hC,
      eventually_ge_atTop (1 : ℕ)] with M hpotential hM
  intro L q
  have hcard := timeoutFeasibleTimes_card_le_potential P K₀
    (L := L) (S := shrinkingSwitchRank C M) (q := q) hM
  have hpot0 := timeoutTimePotential_nonneg P M
    (shrinkingSwitchRank C M) (M + 1)
  have hceil :
      (⌈(1 + 2 * timeoutTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
        driftGap)⌉₊ : ℝ) <
      (1 + 2 * timeoutTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
        driftGap) + 1 := by
    apply Nat.ceil_lt_add_one
    have hquot : 0 ≤
        2 * timeoutTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
          driftGap := div_nonneg (mul_nonneg (by norm_num) hpot0) driftGap_pos.le
    linarith
  have hcardR :
      ((timeoutFeasibleTimes P K₀ L M (shrinkingSwitchRank C M) q).card : ℝ) ≤
        (⌈(1 + 2 * timeoutTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
          driftGap)⌉₊ : ℝ) := by exact_mod_cast hcard
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
  calc
    ((timeoutFeasibleTimes P K₀ L M (shrinkingSwitchRank C M) q).card : ℝ) ≤
        (⌈(1 + 2 * timeoutTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
          driftGap)⌉₊ : ℝ) := hcardR
    _ < (1 + 2 * timeoutTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
          driftGap) + 1 := hceil
    _ ≤ timeoutTimeSupportConstant P C *
          Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) + 1 := by
      linarith
    _ ≤ (timeoutTimeSupportConstant P C + 1) *
          Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
      nlinarith
end FirstPassageLinearTransport
