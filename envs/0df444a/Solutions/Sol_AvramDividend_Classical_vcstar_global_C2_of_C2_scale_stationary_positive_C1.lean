-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_global_C2_of_C2_scale_stationary_positive_C1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T08:20:00.217418+00:00
-- url     : https://prove2.me/submissions/99c98d83-f62f-4175-8b73-5f6d5a76622b

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_piecewise_const_of_stationary_join
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_piecewise_ratio_one_of_C1_positive
import Theorems.Thm_AvramDividend_Classical_contDiffOn_two_of_deriv_eq_C1
open Set

theorem solution
    (W : ℝ → ℝ)
    (hcpos : 0 < (AvramDividend.Classical.cstar W).toReal)
    (hW2 : ContDiffOn ℝ 2 W (Ioi (0 : ℝ)))
    (hdpos : 0 < deriv W (AvramDividend.Classical.cstar W).toReal)
    (hflat : deriv (deriv W) (AvramDividend.Classical.cstar W).toReal = 0)
    (hvc1 : ContDiffOn ℝ 1 (AvramDividend.Classical.vcstar W) (Ioi (0 : ℝ))) :
    ContDiffOn ℝ 2 (AvramDividend.Classical.vcstar W) (Ioi (0 : ℝ)) := by
  set c := (AvramDividend.Classical.cstar W).toReal with hc
  have hW' : ContDiffOn ℝ 1 (deriv W) (Ioi (0 : ℝ)) :=
    hW2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hg := AvramDividend.Classical.contDiffOn_one_piecewise_const_of_stationary_join
    (fun y => deriv W y / deriv W c) c 1 hcpos (hW'.div_const _)
    (by rw [deriv_div_const, hflat, zero_div]) (div_self hdpos.ne')
  exact AvramDividend.Classical.contDiffOn_two_of_deriv_eq_C1 _ _
    (hvc1.differentiableOn one_ne_zero) hg
    (AvramDividend.Classical.vcstar_deriv_piecewise_ratio_one_of_C1_positive W hcpos
      (hW2.of_le (by norm_num)) hdpos)
