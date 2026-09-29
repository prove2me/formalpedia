-- Prove2me | solution 1 for Erdos52.sumset_card_ge_two_mul_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:18:19.354052+00:00
-- url     : https://prove2.me/submissions/c832ce91-315c-4e50-aa74-0500d2a074b2

import Mathlib
open scoped Pointwise

namespace Erdos52
end Erdos52

open Erdos52

theorem solution (A : Finset ℤ) (hA : A.Nonempty) :
    2 * A.card - 1 ≤ (A + A).card := by
  have h := cauchy_davenport_add_of_linearOrder_isCancelAdd hA hA
  rw [two_mul]
  exact h
