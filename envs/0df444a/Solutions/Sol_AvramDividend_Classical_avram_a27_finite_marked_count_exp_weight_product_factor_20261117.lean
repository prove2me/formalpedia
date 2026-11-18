-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_finite_marked_count_exp_weight_product_factor_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T19:05:24.898442+00:00
-- url     : https://prove2.me/submissions/9d6df802-a774-47bf-9527-618ce4098eca

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped BigOperators
noncomputable section

/-- A finite physical marked point configuration's joint count and Laplace factor is its pointwise marked product. -/
theorem solution
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (z θ : ℝ) (y : ι → ℝ) :
    z ^ S.card * S.prod (fun i => Real.exp (θ * y i)) =
      S.prod (fun i => z * Real.exp (θ * y i)) := by
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const]
