-- Prove2me | solution 1 for AvramDividend.Classical.positive_laplace_linear_reference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T16:46:48.906589+00:00
-- url     : https://prove2.me/submissions/55e05ccd-4067-46fc-9ceb-fc8522106687

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem solution (θ : ℝ) (hθ : 0 < θ) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * x ∂volume) =
      (1 / θ) ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (2 : ℝ)) (r := θ) (by norm_num) hθ
  simpa [Real.Gamma_two, show (2 : ℝ) - 1 = 1 by norm_num,
    Real.rpow_one, mul_comm] using h
