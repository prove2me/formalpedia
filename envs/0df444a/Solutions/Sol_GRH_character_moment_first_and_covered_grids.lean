-- Prove2me | solution 1 for GRH.character_moment_first_and_covered_grids
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T17:30:47.2179+00:00
-- url     : https://prove2.me/submissions/933ed72e-1f4e-43be-8c65-aa23c0b1e93f

import Theorems.Thm_GRH_dirichlet_nonzero_of_character_moment_cover
import Theorems.Thm_GRH_character_moment_rectangle_at_sixty_six
import Theorems.Thm_GRH_character_moment_rectangle_at_seventy_eight
import Theorems.Thm_GRH_dirichlet_rectangle_nonzero_iff_finite_grid
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open GRH.DirichletGrid

/-- The convolution test gives the target grid wherever it passes. On the
first grid it applies to every divisor of 66 or 78, including 11 and 13. -/
theorem solution (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1)
    (h : ℕ) (hp : (h=0 ∧ (d ∣ 66 ∨ d ∣ 78)) ∨ GRH.CharacterMoment.Covers d
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
  have cover : GRH.CharacterMoment.Covers d a (0.8749570698:ℝ) ((h:ℝ)+1) := by
    rcases hp with ⟨rfl,hd|hd⟩ | hgood
    · apply GRH.character_moment_rectangle_at_sixty_six d hd <;> norm_num [a]
    · apply GRH.character_moment_rectangle_at_seventy_eight d hd <;> norm_num [a]
    · exact hgood
  apply (GRH.dirichlet_rectangle_nonzero_iff_finite_grid d χ hχ a _ _
    hleft hright (by norm_num) (by positivity)).1
  intro z hz
  exact GRH.dirichlet_nonzero_of_character_moment_cover d χ hχ a _ _ cover z
    hz.1.1 hz.1.2 (abs_le.mpr hz.2)
