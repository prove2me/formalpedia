-- Prove2me | solution 1 for FirstPassageLinearTransport.lowTimeout_duration_error_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:09:36.548006+00:00
-- url     : https://prove2.me/submissions/ba2bd787-6f43-4546-a7a4-e5e501c9492c

import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
import Theorems.Thm_FirstPassageLinearTransport_a0_lt_one
import Theorems.Thm_FirstPassageLinearTransport_driftGap_lt_a0
import Theorems.Thm_FirstPassageLinearTransport_driftGap_pos


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {K₀ : ℝ} {L S m x : ℕ}
    (hmS : m < S) (hpass : LowTimeoutPassage K₀ L m x)
    (hqparent : timeoutTargetRank K₀ L m < m) :
    |driftGap * (hpass.duration : ℝ) -
        ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ))| + 1 ≤ S := by
  have hgap0 : 0 ≤ driftGap := driftGap_pos.le
  have hgap1 : driftGap ≤ 1 := by
    linarith [driftGap_lt_a0, a0_lt_one]
  have hduration : (hpass.duration : ℝ) ≤ m := by
    exact_mod_cast hpass.duration_le
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hq0 : (0 : ℝ) ≤ timeoutTargetRank K₀ L m := Nat.cast_nonneg _
  have hprod0 : 0 ≤ driftGap * (hpass.duration : ℝ) :=
    mul_nonneg hgap0 (Nat.cast_nonneg _)
  have hprodM : driftGap * (hpass.duration : ℝ) ≤ m := by
    nlinarith
  have hdiff0 : 0 ≤ (m : ℝ) - (timeoutTargetRank K₀ L m : ℝ) := by
    have hqm : (timeoutTargetRank K₀ L m : ℝ) ≤ m := by
      exact_mod_cast hqparent.le
    linarith
  have hdiffM : (m : ℝ) - (timeoutTargetRank K₀ L m : ℝ) ≤ m := by
    linarith
  have habs :
      |driftGap * (hpass.duration : ℝ) -
        ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ))| ≤ m := by
    rw [abs_le]
    constructor <;> linarith
  have hmSreal : (m : ℝ) + 1 ≤ S := by exact_mod_cast hmS
  linarith
end FirstPassageLinearTransport
