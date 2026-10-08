-- Prove2me | solution 1 for AvramDividend.Classical.deriv_near_zero_strict_of_liminf_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T16:33:03.409084+00:00
-- url     : https://prove2.me/submissions/4458787f-e54e-4acd-b8f1-bcf5c88620ef

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical Filter
open scoped Topology

theorem solution (W : ℝ → ℝ) (a : ℝ)
    (hgap : ((deriv W a : ℝ) : EReal) < derivZeroPlus W) :
    ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), deriv W a < deriv W x := by
  unfold derivZeroPlus at hgap
  have hevent :
      ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
        ((deriv W a : ℝ) : EReal) < ((deriv W x : ℝ) : EReal) :=
    eventually_lt_of_lt_liminf hgap
  filter_upwards [hevent] with x hx
  exact EReal.coe_lt_coe_iff.mp hx
