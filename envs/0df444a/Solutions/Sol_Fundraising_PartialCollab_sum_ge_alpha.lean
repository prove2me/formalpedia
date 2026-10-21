-- Prove2me | solution 1 for Fundraising.PartialCollab.sum_ge_alpha
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:17:31.674779+00:00
-- url     : https://prove2.me/submissions/35858261-bc19-4ea0-9eb5-15053560ce9f

import Mathlib
set_option autoImplicit false

open Finset

theorem solution {n : ℕ} [NeZero n] (α x : Fin n → ℝ) (hα : Antitone α)
    (hx : ∀ i, x i = max (α i - ∑ j ∈ univ.erase i, x j) 0) :
    α 0 ≤ ∑ i, x i := by
  have h0 := hx 0
  have hs : ∑ j ∈ univ.erase (0 : Fin n), x j + x 0 = ∑ i, x i :=
    Finset.sum_erase_add _ _ (Finset.mem_univ _)
  have h1 : α 0 - ∑ j ∈ univ.erase (0 : Fin n), x j ≤ x 0 := by
    rw [h0]; exact le_max_left _ _
  linarith
