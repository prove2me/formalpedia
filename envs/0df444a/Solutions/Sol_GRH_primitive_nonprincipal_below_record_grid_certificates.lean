-- Prove2me | solution 1 for GRH.primitive_nonprincipal_below_record_grid_certificates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T15:43:49.758319+00:00
-- url     : https://prove2.me/submissions/577a1979-802d-488e-8b9e-691e448d371f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_dirichlet_grid_of_period_cover
import Theorems.Thm_GRH_first_two_dirichlet_grids_at_small_levels
import Theorems.Thm_GRH_primitive_dirichlet_grids_outside_period_covers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem solution
    (d : ℕ) [NeZero d] (ψ : DirichletCharacter ℂ d) (hprim : ψ.IsPrimitive) (hψ : ψ ≠ 1)
    (h : ℕ) : ∃ m : ℕ, GRH.DirichletGrid.Passes ψ
      (1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) (0.8749570698:ℝ) ((h:ℝ)+1) m := by
  by_cases e : (h=0 ∧ (d ∣ 8 ∨ d ∣ 12 ∨ d ∣ 18 ∨ d ∣ 30)) ∨ (h=1 ∧ (d ∣ 4 ∨ d ∣ 6))
  · exact GRH.first_two_dirichlet_grids_at_small_levels d ψ hψ h e
  · let a := 1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)
    by_cases hw : GRH.DirichletPeriod.Covers d a ((h:ℝ)+1)
    · have hpos : (0:ℝ) ≤ (0.8749570698:ℝ)-1/2 := by norm_num
      have hleft : (1/2:ℝ) ≤ a := le_add_of_nonneg_right (div_nonneg hpos (by positivity))
      have hright : a ≤ (0.8749570698:ℝ) := by
        have hdiv := div_le_self hpos (show 1 ≤ (h:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) h])
        dsimp [a]
        linarith
      exact GRH.dirichlet_grid_of_period_cover d ψ hψ a _ _ hleft hright (by norm_num) (by positivity) hw
    · exact GRH.primitive_dirichlet_grids_outside_period_covers d ψ hprim hψ h hw
