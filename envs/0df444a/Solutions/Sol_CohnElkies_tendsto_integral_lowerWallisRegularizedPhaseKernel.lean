-- Prove2me | solution 1 for CohnElkies.tendsto_integral_lowerWallisRegularizedPhaseKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/a67d9960-119d-4b07-8947-800c20f4da88

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerWallisRegularizedPhaseKernel_abs_le_moment
import Theorems.Thm_CohnElkies_lowerWallisRegularizedPhaseKernel_abs_le_tail
import Theorems.Thm_CohnElkies_lowerWallisRegularizedPhaseMajorant_integrable

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution
    (u : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ∫ t : ℝ in Ioi 0,
          lowerWallisRegularizedPhaseKernel
            (1 / ((n : ℝ) + 1)) u t)
      atTop
      (𝓝 (∫ t : ℝ in Ioi 0, lowerWallisPhaseKernel u t)) := by
  apply tendsto_integral_of_dominated_convergence
    (lowerWallisRegularizedPhaseMajorant u)
  · intro n
    exact
      (show Measurable
        (fun t : ℝ =>
          lowerWallisRegularizedPhaseKernel
            (1 / ((n : ℝ) + 1)) u t) by
        unfold lowerWallisRegularizedPhaseKernel
        fun_prop).aestronglyMeasurable
  · exact lowerWallisRegularizedPhaseMajorant_integrable u
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with t ht
    have hapos : 0 < 1 / ((n : ℝ) + 1) := by
      positivity
    have haone : 1 / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ (show 0 < (n : ℝ) + 1 by positivity)).2
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith
    rw [Real.norm_eq_abs]
    by_cases htone : t ≤ 1
    · simp only [lowerWallisRegularizedPhaseMajorant,
        if_pos htone]
      exact lowerWallisRegularizedPhaseKernel_abs_le_moment
        hapos.le haone u ht
    · simp only [lowerWallisRegularizedPhaseMajorant,
        if_neg htone]
      exact lowerWallisRegularizedPhaseKernel_abs_le_tail
        hapos.le u (le_of_not_ge htone)
  · filter_upwards [] with t
    have hcontinuous :
        Continuous
          (fun a : ℝ => lowerWallisRegularizedPhaseKernel a u t) := by
      unfold lowerWallisRegularizedPhaseKernel
      fun_prop
    have hzero :
        lowerWallisRegularizedPhaseKernel 0 u t =
          lowerWallisPhaseKernel u t := by
      unfold lowerWallisRegularizedPhaseKernel
        lowerWallisPhaseKernel
      simp
    rw [← hzero]
    exact hcontinuous.continuousAt.tendsto.comp
      tendsto_one_div_add_atTop_nhds_zero_nat
end CohnElkies
