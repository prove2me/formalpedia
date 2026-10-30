-- Prove2me | solution 1 for AvramDividend.Classical.discounted_remainder_vanishes_of_positive_discount_3e1c_gap
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T10:53:05.14419+00:00
-- url     : https://prove2.me/submissions/e629dc75-ab55-415a-ad25-d3a1c00c59ed

import Mathlib
open Filter Topology

theorem solution
    (q C : ℝ) (hq : 0 < q) :
    Filter.Tendsto (fun t : ℝ => Real.exp (-(q * t)) * C) Filter.atTop (nhds 0) := by
  have h1 : Tendsto (fun t : ℝ => q * t) atTop atTop := tendsto_id.const_mul_atTop hq
  have h2 : Tendsto (fun t : ℝ => -(q * t)) atTop atBot := tendsto_neg_atTop_atBot.comp h1
  have h3 : Tendsto (fun t : ℝ => Real.exp (-(q * t))) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp h2
  simpa using h3.mul_const C
