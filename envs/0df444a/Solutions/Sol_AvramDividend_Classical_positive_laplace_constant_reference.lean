-- Prove2me | solution 1 for AvramDividend.Classical.positive_laplace_constant_reference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T17:08:00.862105+00:00
-- url     : https://prove2.me/submissions/f6211828-c60b-4606-8e6d-3c440cf9e02a

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

theorem solution (θ : ℝ) (hθ : 0 < θ) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ * x))) (Ioi (0 : ℝ)) volume ∧
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) ∂volume) = 1 / θ := by
  have hn : -θ < 0 := neg_neg_iff_pos.mpr hθ
  constructor
  · simpa only [neg_mul] using
      (integrableOn_exp_mul_Ioi (a := -θ) hn (0 : ℝ))
  · have h := integral_exp_mul_Ioi (a := -θ) hn (0 : ℝ)
    have h' : (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) ∂volume) =
        -Real.exp (-θ * 0) / -θ := by
      simpa only [neg_mul] using h
    rw [h']
    simp
