-- Prove2me | solution 1 for AvramDividend.Classical.positive_laplace_linear_reference_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T16:59:50.481824+00:00
-- url     : https://prove2.me/submissions/9b002041-a010-496e-a6d8-e5e370ec152b

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem solution (θ : ℝ) (hθ : 0 < θ) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * x)
      (Ioi (0 : ℝ)) volume := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (1 : ℝ)) (b := θ)
    (by norm_num) (by norm_num) hθ
  have hfun :
      (fun x : ℝ => Real.exp (-(θ * x)) * x) =
        (fun x : ℝ => x ^ (1 : ℝ) *
          Real.exp (-θ * x ^ (1 : ℝ))) := by
    funext x
    simp only [Real.rpow_one]
    have hm : -θ * x = -(θ * x) := by ring
    rw [hm]
    ring
  rw [hfun]
  exact h
