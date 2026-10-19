-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryLog_dimension_scaled_le_neg_of_large
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/fd95ff0b-fb05-4d07-8369-eedd4ac4eb1c

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerCoth_log_le_four_exp_neg_two
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_dimension_scaled_log_tail_uniform

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
    {d : ℕ} (hd : 2 ≤ d) {c Y n : ℝ}
    (hc : 0 < c) (hn : 0 ≤ n)
    (hlarge : max 1 (8 * Real.pi * c ^ 2 * Real.exp n) ≤ |Y|) :
    lowerGammaBoundaryLog ((d : ℝ) / 2)
      (c * Real.sqrt d) (((d : ℝ) / 2) * Y) ≤ -n := by
  have hyone : 1 ≤ |Y| :=
    le_trans (le_max_left 1 _) hlarge
  have hY : Y ≠ 0 := by
    intro h
    norm_num [h] at hyone
  have hA : 0 < 4 * Real.pi * c ^ 2 := by positivity
  have hden : 0 < |Y| := abs_pos.mpr hY
  have hradius : 8 * Real.pi * c ^ 2 * Real.exp n ≤ |Y| :=
    le_trans (le_max_right 1 _) hlarge
  have hexpcancel : Real.exp n * Real.exp (-n) = 1 := by
    rw [Real.exp_neg, mul_inv_cancel₀ (Real.exp_ne_zero n)]
  have hscaled := mul_le_mul_of_nonneg_right
    hradius (Real.exp_pos (-n)).le
  have hratio :
      4 * Real.pi * c ^ 2 / |Y| ≤
        (1 / 2 : ℝ) * Real.exp (-n) := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hratio_pos : 0 < 4 * Real.pi * c ^ 2 / |Y| :=
    div_pos hA hden
  have hlogratio :
      Real.log (4 * Real.pi * c ^ 2 / |Y|) ≤
        -(Real.log (2 : ℝ)) - n := by
    calc
      Real.log (4 * Real.pi * c ^ 2 / |Y|) ≤
          Real.log ((1 / 2 : ℝ) * Real.exp (-n)) :=
        Real.log_le_log hratio_pos hratio
      _ = -(Real.log (2 : ℝ)) - n := by
        rw [Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0)
          (Real.exp_ne_zero _), Real.log_exp,
          one_div, Real.log_inv]
        ring
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log (2 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos
      (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hpiabs : 3 ≤ Real.pi * |Y| := by
    nlinarith [Real.pi_gt_three,
      mul_nonneg (by linarith [Real.pi_gt_three] : 0 ≤ Real.pi - 3)
        (sub_nonneg.mpr hyone)]
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
  have hcorrection :
      (1 / 2 : ℝ) *
          Real.log (lowerCoth (Real.pi * |Y| / 2)) ≤
        (1 / 2 : ℝ) := by
    nlinarith
  have hℓ : 1 ≤ (d : ℝ) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    exact_mod_cast hd
  have hlognonneg : 0 ≤ Real.log (2 : ℝ) + n := by
    linarith
  have hmain :
      ((d : ℝ) / 2) *
        Real.log (4 * Real.pi * c ^ 2 / |Y|) ≤
          -(Real.log (2 : ℝ)) - n := by
    calc
      ((d : ℝ) / 2) *
          Real.log (4 * Real.pi * c ^ 2 / |Y|) ≤
        ((d : ℝ) / 2) * (-(Real.log (2 : ℝ)) - n) :=
        mul_le_mul_of_nonneg_left hlogratio (by positivity)
      _ ≤ -(Real.log (2 : ℝ)) - n := by
        nlinarith [mul_nonneg
          (sub_nonneg.mpr hℓ) hlognonneg]
  have htail := lowerGammaBoundaryLog_dimension_scaled_log_tail_uniform
    hd hc hY
  linarith
end CohnElkies
