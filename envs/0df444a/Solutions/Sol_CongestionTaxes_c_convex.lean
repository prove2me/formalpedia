-- Prove2me | solution 1 for CongestionTaxes.c_convex
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:24:23.908765+00:00
-- url     : https://prove2.me/submissions/d73ac52b-0515-4400-9b64-cf4b1997e849

import Mathlib
import Definitions.Def_CongestionTaxes_Assumption1

open CongestionTaxes in
theorem solution (ℓ : ℕ → ℝ) (hℓ : Assumption1 ℓ) (x : ℕ) :
    2 * (((x : ℝ) + 1) * ℓ (x + 1)) ≤ ((x : ℝ) + 2) * ℓ (x + 2) + (x : ℝ) * ℓ x := by
  obtain ⟨h0, _, h3, h4⟩ := hℓ
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx
    have := h3 1 le_rfl
    norm_num at this ⊢
    linarith
  · have := h4 x hx
    linarith
