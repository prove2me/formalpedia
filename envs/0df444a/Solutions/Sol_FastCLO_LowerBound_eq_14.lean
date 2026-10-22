-- Prove2me | solution 1 for FastCLO.LowerBound.eq_14
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:25:15.660805+00:00
-- url     : https://prove2.me/submissions/b8b8a885-130d-41df-8ef3-ab8d3319cee7

import Mathlib
set_option autoImplicit false

theorem solution {Ω : Type*} [Fintype Ω] (w0 w1 : Ω → ℝ) (h0 : ∀ ω, 0 ≤ w0 ω) (h1 : ∀ ω, 0 ≤ w1 ω)
    (bhat : Ω → Bool) :
    ∑ ω, min (w0 ω) (w1 ω) ≤ ∑ ω, (if bhat ω then w0 ω else w1 ω) := by
  apply Finset.sum_le_sum
  intro ω _
  cases bhat ω
  · exact min_le_right _ _
  · exact min_le_left _ _
