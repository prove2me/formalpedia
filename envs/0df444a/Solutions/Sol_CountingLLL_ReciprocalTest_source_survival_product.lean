-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.source_survival_product
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:16:27.242874+00:00
-- url     : https://prove2.me/submissions/d1c7f43c-3a1b-4c41-b51e-61f0d6b7ac9a

import Mathlib
set_option autoImplicit false
open scoped BigOperators

theorem solution (n : ℕ) :
    (∏ i ∈ Finset.range n, (1 - 1 / ((i+2 : ℕ) : ℝ))) = 1 / ((n+1 : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    push_cast
    have h1 : (n : ℝ)+1 ≠ 0 := by positivity
    have h2 : (n : ℝ)+2 ≠ 0 := by positivity
    field_simp
    <;> ring
