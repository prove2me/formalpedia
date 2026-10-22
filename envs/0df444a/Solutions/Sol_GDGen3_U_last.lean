-- Prove2me | solution 1 for GDGen3.U_last
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:14:21.087985+00:00
-- url     : https://prove2.me/submissions/5f5ed1a1-15f6-4b4c-8510-eb41b53fc3fb

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_Abar_ne_zero
import Theorems.Thm_GDGen3_ell_of_lt
import Theorems.Thm_GDGen3_am_telescope

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (N : ℕ) (hN : 1 ≤ N) (ξ : ℕ → ℝ) (h0 : ξ 0 = 0)
    (hpos : ∀ i : ℕ, i ≠ 0 → 0 < ξ i) : U r ξ N N = pj r N := by
  have ht : ∀ j ∈ range N, ell r ξ N j N =
      (Abar ξ j - Am ξ j) * (D r ξ N N + r * D r ξ N (N + 1)) := by
    intro j hj; exact ell_of_lt r ξ N (mem_range.mp hj)
  unfold U
  rw [sum_congr rfl ht, ← sum_mul]
  have hid : N - 1 + 1 = N := by omega
  have ha := am_telescope ξ (N - 1)
  rw [hid] at ha
  rw [ha]
  have hDN1 : D r ξ N (N + 1) = 0 := by simp [D]
  rw [hDN1, mul_zero, add_zero]
  simp only [D, if_neg (by omega : ¬(N = 0 ∨ N < N)),
    Am, if_neg (by omega : N ≠ 0)]
  exact mul_div_cancel₀ _ (Abar_ne_zero ξ h0 hpos (N - 1))
