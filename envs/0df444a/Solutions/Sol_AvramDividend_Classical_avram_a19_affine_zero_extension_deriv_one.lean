-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_affine_zero_extension_deriv_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:34:59.242256+00:00
-- url     : https://prove2.me/submissions/d042ed81-6a91-45e9-b0a1-f5d25e8fd6d0

import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Defs
import Theorems.Thm_AvramDividend_Classical_avram_gen11_piecewise_affine_positive_deriv_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter

/-- Reuse the proved source positive-reserve derivative identity in the original A19 leaf. -/
theorem solution (x : ℝ) (hx : 0 < x) :
    deriv (fun y : ℝ => if y < 0 then (0 : ℝ) else 1 + y) x = 1 := by
  exact AvramDividend.Classical.avram_gen11_piecewise_affine_positive_deriv_one x hx
