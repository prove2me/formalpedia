-- Prove2me | solution 1 for GRH.primitive_dirichlet_grids_outside_weighted_energy
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T18:49:02.257968+00:00
-- url     : https://prove2.me/submissions/3b8be4de-d2ea-4d4c-90ec-e2617663ae86
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_primitive_dirichlet_grid_of_dyadic_representatives
import Theorems.Thm_GRH_dirichlet_grid_inverse_and_reflected_cells
import Theorems.Thm_GRH_quartic_twenty_nine_conjugate_first_grids
import Theorems.Thm_GRH_dirichlet_grid_of_period_cover
import Theorems.Thm_GRH_dirichlet_grid_of_weighted_prefix_cover
import Theorems.Thm_GRH_dirichlet_nonzero_of_character_moment_cover
import Theorems.Thm_GRH_dirichlet_nonzero_of_weighted_character_energy
import Theorems.Thm_GRH_dirichlet_rectangle_nonzero_iff_finite_grid
import Theorems.Thm_GRH_primitive_dirichlet_dyadic_representative_certificates
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open GRH.DyadicCharacterGrid GRH.DirichletGrid

private theorem certified_grid (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d)
    (hprim : χ.IsPrimitive) (hne : χ≠1) (h : ℕ) :
    ∃ m : ℕ, Passes χ (left (0.8749570698:ℝ) h) (0.8749570698:ℝ) ((h:ℝ)+1) m := by
  apply GRH.primitive_dirichlet_grid_of_dyadic_representatives χ hprim hne (0.8749570698:ℝ)
    (by norm_num) (by norm_num) ?_ h
  intro ψ hp hn ho k
  let b : ℝ := 0.8749570698
  let a := left b (index k)
  let H := (index k:ℝ)+1
  have hm : 1≤H := by dsimp [H];linarith [Nat.cast_nonneg (α:=ℝ) (index k)]
  have hh : 0≤H := by linarith
  have hpos : (0:ℝ)≤b-1/2 := by norm_num [b]
  have ha : (1/2:ℝ)≤a := le_add_of_nonneg_right (div_nonneg hpos hh)
  have hab : a≤b := by
    have v := div_le_self hpos hm
    change 1/2+(b-1/2)/H≤b
    linarith
  have pack (g : ∃ m : ℕ, Passes ψ a b H m) : ∃ m : ℕ, Checks ψ a b H m := by
    obtain ⟨m,hm⟩ := g
    exact ⟨m,(GRH.dirichlet_grid_inverse_and_reflected_cells ψ a b H m).2.2 hm⟩
  by_cases h29 : index k=0 ∧ d=29 ∧ (ψ 2=Complex.I ∨ ψ 2= -Complex.I)
  · rcases h29 with ⟨e,rfl,hv⟩
    apply pack (GRH.quartic_twenty_nine_conjugate_first_grids ψ hv a b H hab (by norm_num [b]) hh ?_)
    exact Or.inl ⟨by norm_num [a,left,b,e],by norm_num [H,e]⟩
  by_cases hg : GRH.DirichletPeriod.Covers d a H
  · exact pack (GRH.dirichlet_grid_of_period_cover d ψ hn a b H ha hab (by norm_num [b]) hh hg)
  by_cases hw : GRH.DirichletPrefix.Covers d a b H
  · exact pack (GRH.dirichlet_grid_of_weighted_prefix_cover d ψ hn a b H ha hab (by norm_num [b]) hh hw)
  by_cases hmom : GRH.CharacterMoment.Covers d a b H
  · apply pack ((GRH.dirichlet_rectangle_nonzero_iff_finite_grid d ψ hn a b H ha hab (by norm_num [b]) hh).1 ?_)
    exact fun z hz => GRH.dirichlet_nonzero_of_character_moment_cover d ψ hn a b H hmom z hz.1.1 hz.1.2 (abs_le.mpr hz.2)
  by_cases he : GRH.WeightedEnergy.Covers d a b H
  · apply pack ((GRH.dirichlet_rectangle_nonzero_iff_finite_grid d ψ hn a b H ha hab (by norm_num [b]) hh).1 ?_)
    exact fun z hz => GRH.dirichlet_nonzero_of_weighted_character_energy d ψ hn a b H he z hz.1.1 hz.1.2 (abs_le.mpr hz.2)
  exact GRH.primitive_dirichlet_dyadic_representative_certificates d ψ hp hn ho k hg hw hmom he h29

theorem solution
    (d : ℕ) [NeZero d] (ψ : DirichletCharacter ℂ d) (hprim : ψ.IsPrimitive) (hψ : ψ ≠ 1)
    (h : ℕ) (_hgap : ¬ GRH.DirichletPeriod.Covers d
      (1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) ((h:ℝ)+1))
    (_hweight : ¬ GRH.DirichletPrefix.Covers d
      (1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) (0.8749570698:ℝ) ((h:ℝ)+1))
    (_hmoment : ¬ GRH.CharacterMoment.Covers d
      (1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) (0.8749570698:ℝ) ((h:ℝ)+1))
    (_henergy : ¬ GRH.WeightedEnergy.Covers d
      (1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) (0.8749570698:ℝ) ((h:ℝ)+1)) :
    ∃ m : ℕ, GRH.DirichletGrid.Passes ψ
      (1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) (0.8749570698:ℝ) ((h:ℝ)+1) m := by
  exact certified_grid d ψ hprim hψ h
