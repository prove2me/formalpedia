-- Prove2me | solution 1 for GRH.primitive_dirichlet_grids_outside_both_prefix_tests
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T17:28:41.340692+00:00
-- url     : https://prove2.me/submissions/2ada6c46-54e4-40e1-b75c-3db1d9d28b74
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_character_moment_first_and_covered_grids
import Theorems.Thm_GRH_primitive_dirichlet_grids_outside_character_moments
import Definitions.Def_GRH_DirichletGrid
import Definitions.Def_GRH_DirichletPeriod
import Definitions.Def_GRH_DirichletPrefix

theorem solution
    (d : ℕ) [NeZero d] (ψ : DirichletCharacter ℂ d) (hprim : ψ.IsPrimitive) (hψ : ψ ≠ 1)
    (h : ℕ) (hgap : ¬ GRH.DirichletPeriod.Covers d
      (1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) ((h:ℝ)+1))
    (hweight : ¬ GRH.DirichletPrefix.Covers d
      (1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) (0.8749570698:ℝ) ((h:ℝ)+1)) :
    ∃ m : ℕ, GRH.DirichletGrid.Passes ψ
      (1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) (0.8749570698:ℝ) ((h:ℝ)+1) m := by
  let a := 1/2+((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)
  by_cases hnew : h=0 ∧ (d ∣ 66 ∨ d ∣ 78)
  · exact GRH.character_moment_first_and_covered_grids d ψ hψ h (Or.inl hnew)
  by_cases hm : GRH.CharacterMoment.Covers d a (0.8749570698:ℝ) ((h:ℝ)+1)
  · exact GRH.character_moment_first_and_covered_grids d ψ hψ h (Or.inr hm)
  exact GRH.primitive_dirichlet_grids_outside_character_moments d ψ hprim hψ h hgap hweight hm
