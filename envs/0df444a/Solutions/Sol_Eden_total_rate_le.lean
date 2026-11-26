-- Prove2me | solution 1 for Eden.total_rate_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:05:50.981275+00:00
-- url     : https://prove2.me/submissions/9cd5550f-03e1-4c94-bb61-5748b38ef313

import Definitions.Def_Eden_Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Eden_Algebra
import Theorems.Thm_Eden_total_rate_identity

set_option autoImplicit true
open Eden
namespace Eden
theorem _root_.solution (s₁ s₂ c : ℝ) :
    radialRate s₁ + tangentialRate s₁ + radialRate s₂ + tangentialRate s₂ - c ≤
      4 - c := by
  rw [total_rate_identity]
  nlinarith [sq_nonneg (s₁ - 1), sq_nonneg (s₂ - 1)]
end Eden
