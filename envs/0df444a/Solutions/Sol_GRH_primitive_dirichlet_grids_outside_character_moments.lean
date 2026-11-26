-- Prove2me | solution 1 for GRH.primitive_dirichlet_grids_outside_character_moments
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T18:14:20.743394+00:00
-- url     : https://prove2.me/submissions/5819d356-e975-4ebe-94f4-6700999c9c19
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_weighted_energy_first_and_covered_grids
import Theorems.Thm_GRH_primitive_dirichlet_grids_outside_weighted_energy

theorem solution
    (d : ℕ) [NeZero d] (ψ : DirichletCharacter ℂ d) (hprim : ψ.IsPrimitive) (hψ : ψ ≠ 1)
    (h : ℕ) (hgap : ¬ GRH.DirichletPeriod.Covers d
      (1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) ((h:ℝ)+1))
    (hweight : ¬ GRH.DirichletPrefix.Covers d
      (1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) (0.8749570698:ℝ) ((h:ℝ)+1))
    (hmoment : ¬ GRH.CharacterMoment.Covers d
      (1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) (0.8749570698:ℝ) ((h:ℝ)+1)) :
    ∃ m : ℕ, GRH.DirichletGrid.Passes ψ
      (1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) (0.8749570698:ℝ) ((h:ℝ)+1) m := by
  let a := 1/2+((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)
  by_cases hlevels : h=0 ∧ (d ∣ 102 ∨ d ∣ 114)
  · exact GRH.weighted_energy_first_and_covered_grids d ψ hψ h (Or.inl hlevels)
  by_cases he : GRH.WeightedEnergy.Covers d a (0.8749570698:ℝ) ((h:ℝ)+1)
  · exact GRH.weighted_energy_first_and_covered_grids d ψ hψ h (Or.inr he)
  exact GRH.primitive_dirichlet_grids_outside_weighted_energy d ψ hprim hψ h hgap hweight hmoment he
