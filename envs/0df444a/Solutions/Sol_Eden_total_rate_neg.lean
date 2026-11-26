-- Prove2me | solution 1 for Eden.total_rate_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:51:55.212827+00:00
-- url     : https://prove2.me/submissions/5d7a789a-d6e4-410e-b528-fad8158d0746

import Definitions.Def_Eden_Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Eden_Algebra
import Theorems.Thm_Eden_total_rate_le

set_option autoImplicit true
open Eden
namespace Eden
theorem _root_.solution (s₁ s₂ : ℝ) {c : ℝ} (hc : 4 < c) :
    radialRate s₁ + tangentialRate s₁ + radialRate s₂ + tangentialRate s₂ - c < 0 := by
  linarith [total_rate_le s₁ s₂ c]
end Eden
