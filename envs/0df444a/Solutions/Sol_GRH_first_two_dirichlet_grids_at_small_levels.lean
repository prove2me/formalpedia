-- Prove2me | solution 1 for GRH.first_two_dirichlet_grids_at_small_levels
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T15:43:16.156647+00:00
-- url     : https://prove2.me/submissions/d8e74b1b-d3dd-4828-a46f-bb857944f601

import Theorems.Thm_GRH_dirichlet_grid_of_period_cover
import Theorems.Thm_GRH_explicit_small_conductor_period_covers
import Mathlib.Tactic.NormNum

theorem solution (d : ℕ) [NeZero d] (ψ : DirichletCharacter ℂ d) (hψ : ψ ≠ 1)
    (h : ℕ) (hcase : (h=0 ∧ (d ∣ 8 ∨ d ∣ 12 ∨ d ∣ 18 ∨ d ∣ 30)) ∨
      (h=1 ∧ (d ∣ 4 ∨ d ∣ 6))) :
    ∃ m : ℕ, GRH.DirichletGrid.Passes ψ
      (1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) (0.8749570698:ℝ) ((h:ℝ)+1) m := by
  rcases hcase with ⟨rfl,hd⟩ | ⟨rfl,hd⟩
  · apply GRH.dirichlet_grid_of_period_cover d ψ hψ _ _ _ (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
    apply GRH.explicit_small_conductor_period_covers d _ _ (by norm_num)
    exact Or.inl ⟨hd,by norm_num,by norm_num⟩
  · apply GRH.dirichlet_grid_of_period_cover d ψ hψ _ _ _ (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
    apply GRH.explicit_small_conductor_period_covers d _ _ (by norm_num)
    exact Or.inr ⟨hd,Or.inr ⟨by norm_num,by norm_num⟩⟩
