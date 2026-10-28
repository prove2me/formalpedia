-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_deriv_ge_one_zero_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:58:49.727738+00:00
-- url     : https://prove2.me/submissions/3648f3ee-5db3-4c34-9afa-6faf3ddce02d

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_vcstar_smooth_of_zero_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- At a zero optimal barrier the candidate is affine at every positive
reserve, so it is differentiable and its derivative equals one. -/
theorem solution (W : ℝ → ℝ) (hc0 : cstar W = 0) :
    ∀ x : ℝ, 0 < x →
      DifferentiableAt ℝ (vcstar W) x ∧ 1 ≤ deriv (vcstar W) x := by
  intro x hx
  have hsmooth : ContDiffOn ℝ 2 (vcstar W) (Ioi (0 : ℝ)) :=
    vcstar_smooth_of_zero_cstar W hc0
  have hdiffOn : DifferentiableOn ℝ (vcstar W) (Ioi (0 : ℝ)) :=
    hsmooth.differentiableOn (by norm_num)
  have hdiff : DifferentiableAt ℝ (vcstar W) x :=
    (hdiffOn x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)
  have hderiv : deriv (vcstar W) x = 1 := by
    apply vcstar_deriv_eq_one_above_cstar
    simpa [hc0] using hx
  exact ⟨hdiff, hderiv.ge⟩
