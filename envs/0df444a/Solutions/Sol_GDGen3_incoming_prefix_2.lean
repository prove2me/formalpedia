-- Prove2me | solution 2 for GDGen3.incoming_prefix
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:30:38.135603+00:00
-- url     : https://prove2.me/submissions/a295eea8-f221-4dac-8df1-71898c7620bb

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_ell_of_lt
import Theorems.Thm_GDGen3_am_telescope

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (ξ : ℕ → ℝ) (N a b : ℕ) (hab : a < b) :
    (∑ i ∈ range (a + 1), ell r ξ N i b) =
      Abar ξ a * (D r ξ N b + r * D r ξ N (b + 1)) := by
  have ht : ∀ i ∈ range (a + 1), ell r ξ N i b =
      (Abar ξ i - Am ξ i) * (D r ξ N b + r * D r ξ N (b + 1)) := by
    intro i hi
    exact ell_of_lt r ξ N (by simp only [mem_range] at hi; omega)
  rw [sum_congr rfl ht, ← sum_mul, am_telescope]
