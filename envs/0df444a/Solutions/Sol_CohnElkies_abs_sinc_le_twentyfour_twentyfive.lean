-- Prove2me | solution 1 for CohnElkies.abs_sinc_le_twentyfour_twentyfive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/fcd8a321-eba9-4436-850f-9798210feae9

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_sin_le_quintic

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution {x : ℝ}
    (hx : (1 / 2 : ℝ) ≤ x) :
    |Real.sinc x| ≤ (24 / 25 : ℝ) := by
  have hxpos : 0 < x := by linarith
  have hhalf : Real.sin (1 / 2 : ℝ) ≤ (12 / 25 : ℝ) := by
    have h := sin_le_quintic (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h ⊢
    linarith
  by_cases hxpi : x ≤ Real.pi
  · have hsin0 := Real.sin_nonneg_of_nonneg_of_le_pi hxpos.le hxpi
    rw [Real.sinc_of_ne_zero hxpos.ne',
      abs_of_nonneg (div_nonneg hsin0 hxpos.le)]
    have hend :
        Real.sin (1 / 2 : ℝ) / (1 / 2 : ℝ) ≤ (24 / 25 : ℝ) := by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1 / 2)).2
      nlinarith
    rcases hx.eq_or_lt with heq | hlt
    · subst x
      exact hend
    · have hslope := strictConcaveOn_sin_Icc.secant_strict_mono
        (a := (0 : ℝ)) (x := (1 / 2 : ℝ)) (y := x)
        ⟨le_rfl, Real.pi_pos.le⟩
        ⟨by norm_num, by linarith [Real.pi_gt_three]⟩
        ⟨hxpos.le, hxpi⟩
        (by norm_num) hxpos.ne' hlt
      simp only [Real.sin_zero, sub_zero] at hslope
      exact hslope.le.trans hend
  · have hbig : Real.pi ≤ x := le_of_not_ge hxpi
    rw [Real.sinc_of_ne_zero hxpos.ne', abs_div,
      abs_of_nonneg hxpos.le]
    apply (div_le_iff₀ hxpos).2
    have hsin := Real.abs_sin_le_one x
    nlinarith [Real.pi_gt_three]
end CohnElkies
