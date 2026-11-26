-- Prove2me | solution 1 for GRH.primitive_dirichlet_grids_outside_period_covers
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T16:19:39.364646+00:00
-- url     : https://prove2.me/submissions/a4d9e972-1b44-476e-99a5-4a886e9ae4fc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_dirichlet_grid_of_weighted_prefix_cover
import Theorems.Thm_GRH_weighted_prefix_first_and_third_grids
import Theorems.Thm_GRH_primitive_dirichlet_grids_outside_both_prefix_tests
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

theorem solution
    (d : ℕ) [NeZero d] (ψ : DirichletCharacter ℂ d) (hprim : ψ.IsPrimitive) (hψ : ψ ≠ 1)
    (h : ℕ) (hremaining : ¬ GRH.DirichletPeriod.Covers d
      (1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) ((h:ℝ)+1)) :
    ∃ m : ℕ, GRH.DirichletGrid.Passes ψ
      (1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) (0.8749570698:ℝ) ((h:ℝ)+1) m := by
  have hpos : (0:ℝ) ≤ (0.8749570698:ℝ)-1/2 := by norm_num
  let a := 1/2+((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)
  have hleft : (1/2:ℝ) ≤ a := le_add_of_nonneg_right (div_nonneg hpos (by positivity))
  have hright : a ≤ (0.8749570698:ℝ) := by
    have hdiv := div_le_self hpos (show 1 ≤ (h:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) h])
    dsimp [a]
    linarith
  by_cases hc : (h=0 ∧ (d ∣ 24 ∨ d ∣ 36 ∨ d ∣ 42 ∨ d ∣ 60)) ∨ (h=2 ∧ d ∣ 6)
  · exact GRH.weighted_prefix_first_and_third_grids d ψ hψ h hc
  by_cases hw : GRH.DirichletPrefix.Covers d a (0.8749570698:ℝ) ((h:ℝ)+1)
  · exact GRH.dirichlet_grid_of_weighted_prefix_cover d ψ hψ a _ _ hleft hright
      (by norm_num) (by positivity) hw
  exact GRH.primitive_dirichlet_grids_outside_both_prefix_tests d ψ hprim hψ h hremaining hw
