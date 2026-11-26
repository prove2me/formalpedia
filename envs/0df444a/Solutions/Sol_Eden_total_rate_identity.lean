-- Prove2me | solution 1 for Eden.total_rate_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:05:19.866084+00:00
-- url     : https://prove2.me/submissions/109279c2-d8a6-42e7-929b-8c086a234df9

import Definitions.Def_Eden_Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Eden_Algebra

set_option autoImplicit true
open Eden
namespace Eden
theorem _root_.solution (s₁ s₂ c : ℝ) :
    radialRate s₁ + tangentialRate s₁ + radialRate s₂ + tangentialRate s₂ - c =
      4 - c - 6 * (s₁ - 1) ^ 2 - 6 * (s₂ - 1) ^ 2 := by
  unfold radialRate tangentialRate
  ring
end Eden
