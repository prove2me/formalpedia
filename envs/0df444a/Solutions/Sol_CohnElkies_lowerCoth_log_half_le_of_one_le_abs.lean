-- Prove2me | solution 1 for CohnElkies.lowerCoth_log_half_le_of_one_le_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/ca1e63b7-6e5e-4ed2-af51-ca31b015387e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerCoth_log_le_four_exp_neg_two

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution
    {Y : ℝ} (hY : 1 ≤ |Y|) :
    (1 / 2 : ℝ) *
      Real.log (lowerCoth (Real.pi * |Y| / 2)) ≤
        (1 / 2 : ℝ) := by
  have hpiabs : 3 ≤ Real.pi * |Y| := by
    nlinarith [Real.pi_gt_three,
      mul_nonneg
        (by linarith [Real.pi_gt_three] : 0 ≤ Real.pi - 3)
        (sub_nonneg.mpr hY)]
  have harg : 1 ≤ Real.pi * |Y| / 2 := by
    linarith
  have hexpthree : 4 ≤ Real.exp (3 : ℝ) := by
    nlinarith [Real.add_one_le_exp (3 : ℝ)]
  have hexpsmall :
      Real.exp ((-Real.pi) * |Y|) ≤ (1 / 4 : ℝ) := by
    calc
      Real.exp ((-Real.pi) * |Y|) ≤ Real.exp (-3 : ℝ) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = (Real.exp (3 : ℝ))⁻¹ := Real.exp_neg 3
      _ ≤ (1 / 4 : ℝ) := by
        simpa [one_div] using!
          (one_div_le_one_div_of_le
            (by norm_num : (0 : ℝ) < 4) hexpthree)
  have hcoth := lowerCoth_log_le_four_exp_neg_two harg
  have hexp :
      Real.exp (-2 * (Real.pi * |Y| / 2)) =
        Real.exp ((-Real.pi) * |Y|) := by
    congr 1
    ring
  rw [hexp] at hcoth
  nlinarith
end CohnElkies
