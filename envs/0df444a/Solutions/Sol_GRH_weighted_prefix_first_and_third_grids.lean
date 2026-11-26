-- Prove2me | solution 1 for GRH.weighted_prefix_first_and_third_grids
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T16:18:57.652987+00:00
-- url     : https://prove2.me/submissions/f1edefa7-3af5-4826-ab30-9b424f1803f3

import Theorems.Thm_GRH_dirichlet_grid_of_weighted_prefix_cover
import Theorems.Thm_GRH_explicit_weighted_prefix_rectangles
import Mathlib.Tactic.NormNum

open GRH.DirichletGrid

/-- The initial grid holds for all divisors of four witness moduli, and
the third grid holds for every nonprincipal character of level dividing six. -/
theorem solution (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1)
    (h : ℕ) (hc : (h=0 ∧ (d ∣ 24 ∨ d ∣ 36 ∨ d ∣ 42 ∨ d ∣ 60)) ∨ (h=2 ∧ d ∣ 6)) :
    ∃ m : ℕ, Passes χ (1/2+((0.8749570698:ℝ)-1/2)/((h:ℝ)+1))
      (0.8749570698:ℝ) ((h:ℝ)+1) m := by
  rcases hc with ⟨rfl,hd⟩ | ⟨rfl,hd⟩
  · apply GRH.dirichlet_grid_of_weighted_prefix_cover d χ hχ _ _ _ (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
    apply GRH.explicit_weighted_prefix_rectangles d _ _ _ (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    exact Or.inl ⟨hd,by norm_num,by norm_num⟩
  · apply GRH.dirichlet_grid_of_weighted_prefix_cover d χ hχ _ _ _ (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
    apply GRH.explicit_weighted_prefix_rectangles d _ _ _ (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    exact Or.inr ⟨hd,by norm_num,by norm_num⟩
