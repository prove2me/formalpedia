-- Prove2me | solution 1 for GRH.weighted_energy_first_and_covered_grids
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T18:13:20.062799+00:00
-- url     : https://prove2.me/submissions/8e967ad7-0f6b-4a6d-a030-3f18f0c46346

import Theorems.Thm_GRH_dirichlet_nonzero_of_weighted_character_energy
import Theorems.Thm_GRH_weighted_energy_rectangle_at_one_hundred_two
import Theorems.Thm_GRH_weighted_energy_rectangle_at_one_hundred_fourteen
import Theorems.Thm_GRH_dirichlet_rectangle_nonzero_iff_finite_grid
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open GRH.DirichletGrid

/-- The first grid at the divisors of 102 and 114, and every grid where
the weighted character autocorrelation certificate passes. -/
theorem solution (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1)
    (h : ℕ) (hp : (h=0 ∧ (d ∣ 102 ∨ d ∣ 114)) ∨ GRH.WeightedEnergy.Covers d
      (1/2+((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) (0.8749570698:ℝ) ((h:ℝ)+1)) :
    ∃ m : ℕ, Passes χ (1/2+((0.8749570698:ℝ)-1/2)/((h:ℝ)+1))
      (0.8749570698:ℝ) ((h:ℝ)+1) m := by
  let a := 1/2+((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)
  have hpos : (0:ℝ) ≤ (0.8749570698:ℝ)-1/2 := by norm_num
  have hleft : (1/2:ℝ) ≤ a := le_add_of_nonneg_right (div_nonneg hpos (by positivity))
  have hright : a ≤ (0.8749570698:ℝ) := by
    have hdiv := div_le_self hpos (show 1 ≤ (h:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) h])
    dsimp [a]
    linarith
  have cover : GRH.WeightedEnergy.Covers d a (0.8749570698:ℝ) ((h:ℝ)+1) := by
    rcases hp with ⟨rfl,hd|hd⟩ | hgood
    · apply GRH.weighted_energy_rectangle_at_one_hundred_two d hd <;> norm_num [a]
    · apply GRH.weighted_energy_rectangle_at_one_hundred_fourteen d hd <;> norm_num [a]
    · exact hgood
  apply (GRH.dirichlet_rectangle_nonzero_iff_finite_grid d χ hχ a _ _
    hleft hright (by norm_num) (by positivity)).1
  intro z hz
  exact GRH.dirichlet_nonzero_of_weighted_character_energy d χ hχ a _ _ cover z
    hz.1.1 hz.1.2 (abs_le.mpr hz.2)
