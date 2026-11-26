-- Prove2me | solution 1 for FriedCrossing.RateRatio.crossing_value_ne_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:54:45.876854+00:00
-- url     : https://prove2.me/submissions/511fa563-e3a1-461e-80e1-589ced5346e8

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.RateRatio
namespace FriedCrossing.RateRatio
theorem _root_.solution {τR a b : ℝ} (hτR : τR ≠ 0) (ha : a ≠ 0) :
    τR * (b / a) ≠ τR ↔ b ≠ a := by
  rw [Ne, Ne, not_iff_not]
  constructor
  · intro h
    have h' : b / a = 1 := mul_left_cancel₀ hτR (h.trans (mul_one τR).symm)
    exact (div_eq_one_iff_eq ha).mp h'
  · rintro rfl
    rw [div_self ha, mul_one]
end FriedCrossing.RateRatio
