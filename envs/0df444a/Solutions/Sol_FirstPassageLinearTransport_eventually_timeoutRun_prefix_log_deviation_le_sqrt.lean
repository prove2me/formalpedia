-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_timeoutRun_prefix_log_deviation_le_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:28:35.744803+00:00
-- url     : https://prove2.me/submissions/290d63f3-3fae-4d23-a2c9-f5bdc166b2c5

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_prefix_log_deviation_add_potential_le
import Theorems.Thm_FirstPassageLinearTransport_a0_pos
import Theorems.Thm_FirstPassageLinearTransport_driftGap_pos
import Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutTimePotential_source_le_sqrt
import Theorems.Thm_FirstPassageLinearTransport_timeoutTimePotential_nonneg


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : TimeoutHighRunData) {K₀ C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ M : ℕ in atTop, ∀ {L n elapsed q : ℕ},
      TimeoutRecertificationRun P K₀ L M
        (shrinkingSwitchRank C M) n elapsed q →
      ∀ j : ℕ, j ≤ elapsed →
        |shortcutLogDeviation n j| ≤
          timeoutTimeSupportConstant P C *
            Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
  filter_upwards [eventually_timeoutTimePotential_source_le_sqrt P hC,
      eventually_ge_atTop (1 : ℕ)] with M hsupport hM
  intro L n elapsed q hrun j hj
  have htube := hrun.prefix_log_deviation_add_potential_le hM j hj
  have hqPot0 := timeoutTimePotential_nonneg P M
    (shrinkingSwitchRank C M) q
  have hsourcePot0 := timeoutTimePotential_nonneg P M
    (shrinkingSwitchRank C M) (M + 1)
  have hgap1 : driftGap ≤ 1 := by
    unfold driftGap
    linarith [a0_pos]
  have hdiv :
      2 * timeoutTimePotential P M (shrinkingSwitchRank C M) (M + 1) ≤
        2 * timeoutTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
          driftGap := by
    rw [le_div_iff₀ driftGap_pos]
    nlinarith [mul_nonneg hsourcePot0 driftGap_pos.le]
  have hsourceBound :
      2 * timeoutTimePotential P M (shrinkingSwitchRank C M) (M + 1) ≤
        timeoutTimeSupportConstant P C *
          Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by
    calc
      _ ≤ 2 * timeoutTimePotential P M (shrinkingSwitchRank C M) (M + 1) /
          driftGap := hdiv
      _ ≤ 1 + 2 * timeoutTimePotential P M
          (shrinkingSwitchRank C M) (M + 1) / driftGap := by linarith
      _ ≤ _ := hsupport
  linarith
end FirstPassageLinearTransport
