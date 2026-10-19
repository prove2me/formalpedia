-- Prove2me | solution 1 for CohnElkies.tendsto_normalizedVolumeLog_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/a37d467b-bb74-4c1f-8bf2-e452869e88cc

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_tendsto_log_factorial_div_nat_sub_log_nat
import Theorems.Thm_CohnElkies_tendsto_log_nat_sub_log_oddDimension
import Theorems.Thm_CohnElkies_normalizedVolumeLog_odd_eq
import Theorems.Thm_CohnElkies_tendsto_odd_halfDimension_log_correction
import Theorems.Thm_CohnElkies_tendsto_log_oddFactorial_div_oddDimension_sub_log

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Nat Topology
namespace CohnElkies
theorem _root_.solution :
    Tendsto (fun k : ℕ => normalizedVolumeLog (2 * k + 1))
      atTop (nhds ((Real.log (2 * Real.pi) + 1) / 2)) := by
  have hq := Stirling.tendsto_self_div_two_mul_self_add_one
  have hparts :=
    (((((hq.mul_const (Real.log Real.pi)).add
      (tendsto_const_nhds (x := Real.log (2 : ℝ)))).add
      (hq.mul tendsto_log_factorial_div_nat_sub_log_nat)).sub
      tendsto_log_oddFactorial_div_oddDimension_sub_log).add
      tendsto_odd_halfDimension_log_correction).add
      (tendsto_log_nat_sub_log_oddDimension.const_mul (1 / 2 : ℝ))
  have hconstant :
      (1 / 2 : ℝ) * Real.log Real.pi + Real.log 2 +
        (1 / 2 : ℝ) * (-1) - (-1) + 0 +
        (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ) =
          (Real.log (2 * Real.pi) + 1) / 2 := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
    norm_num
    ring
  have hlimit :
      Tendsto
        (fun k : ℕ =>
          (k : ℝ) / (2 * (k : ℝ) + 1) * Real.log Real.pi +
          Real.log 2 +
          ((k : ℝ) / (2 * (k : ℝ) + 1)) *
            (Real.log (k.factorial : ℝ) / (k : ℝ) -
              Real.log (k : ℝ)) -
          (Real.log ((2 * k + 1).factorial : ℝ) /
              (2 * (k : ℝ) + 1) -
            Real.log (2 * (k : ℝ) + 1)) +
          ((k : ℝ) / (2 * (k : ℝ) + 1) - (1 / 2 : ℝ)) *
            Real.log (k : ℝ) +
          (1 / 2 : ℝ) *
            (Real.log (k : ℝ) - Real.log (2 * (k : ℝ) + 1)))
        atTop (nhds ((Real.log (2 * Real.pi) + 1) / 2)) := by
    simpa only [hconstant] using! hparts
  refine hlimit.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  exact (normalizedVolumeLog_odd_eq k hk).symm
end CohnElkies
