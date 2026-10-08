-- Prove2me | solution 1 for AvramDividend.Classical.deriv_global_lower_le_right_liminf
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:38:36.013534+00:00
-- url     : https://prove2.me/submissions/dc008b2e-b825-4bf1-b34f-4e7f649c1181

import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical Filter
open scoped Topology ENNReal

theorem solution (W : ℝ → ℝ) (d : ℝ)
    (hlower : ∀ x : ℝ, 0 < x → d ≤ deriv W x) :
    (d : EReal) ≤ derivZeroPlus W := by
  refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact_mod_cast hlower x hx

#print axioms solution
