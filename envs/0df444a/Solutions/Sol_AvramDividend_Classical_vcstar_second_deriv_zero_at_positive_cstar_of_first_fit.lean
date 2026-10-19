-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_second_deriv_zero_at_positive_cstar_of_first_fit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T07:45:14.84731+00:00
-- url     : https://prove2.me/submissions/c217d7f2-72d6-4217-9556-191edef1335d

import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_deriv_stationary_of_deriv_continuous_differentiable
import Theorems.Thm_AvramDividend_Classical_vcstar_second_deriv_smooth_fit_of_stationary_scale_deriv
import Theorems.Thm_AvramDividend_Classical_scaledW_second_deriv_zero_at_positive_cstar

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution (W : ℝ → ℝ)
    (hc : 0 < (cstar W).toReal)
    (hcont : ContinuousOn (deriv W) (Ioi 0))
    (hWdiff : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ W y)
    (hdne : deriv W (cstar W).toReal ≠ 0)
    (hddiff : DifferentiableAt ℝ (deriv W) (cstar W).toReal)
    (hvderiv : deriv (vcstar W) (cstar W).toReal = 1) :
    deriv (deriv (vcstar W)) (cstar W).toReal = 0 := by
  have hstat : HasDerivAt (deriv W) 0 (cstar W).toReal :=
    cstar_deriv_stationary_of_deriv_continuous_differentiable
      W hcont hc hddiff
  have hmatch := vcstar_second_deriv_smooth_fit_of_stationary_scale_deriv
    W hc hWdiff hdne hstat hvderiv
  exact hmatch.trans
    (scaledW_second_deriv_zero_at_positive_cstar W hcont hc)
