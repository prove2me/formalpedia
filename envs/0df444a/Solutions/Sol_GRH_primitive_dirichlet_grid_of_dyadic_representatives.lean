-- Prove2me | solution 1 for GRH.primitive_dirichlet_grid_of_dyadic_representatives
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T18:46:52.633007+00:00
-- url     : https://prove2.me/submissions/3444bdbb-f74b-4930-aed4-aff8d82c1f3a

import Theorems.Thm_GRH_dirichlet_grid_inverse_and_reflected_cells
import Theorems.Thm_GRH_dirichlet_character_conjugate_representatives
import Theorems.Thm_GRH_dirichlet_grid_of_dyadic_rectangles

open GRH.DyadicCharacterGrid GRH.DirichletGrid

/-- Dyadic certificates for the chosen representatives give the original
rectangular grids for every primitive character and every integer height. -/
theorem solution {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (hp : χ.IsPrimitive) (hn : χ≠1)
    (b : ℝ) (hb : (1/2:ℝ)<b) (hb1 : b≤1)
    (checks : ∀ ψ : DirichletCharacter ℂ d, ψ.IsPrimitive → ψ≠1 → Oriented ψ →
      ∀ k : ℕ, ∃ m : ℕ, Checks ψ (left b (index k)) b ((index k:ℝ)+1) m) :
    ∀ h : ℕ, ∃ m : ℕ, Passes χ (left b h) b ((h:ℝ)+1) m := by
  apply (GRH.dirichlet_grid_of_dyadic_rectangles χ hn b hb hb1).2
  intro k
  let a := left b (index k)
  let H := (index k:ℝ)+1
  rcases (GRH.dirichlet_character_conjugate_representatives χ).1 with good|good
  · obtain ⟨m,hm⟩ := checks χ hp hn good k
    exact ⟨m,(GRH.dirichlet_grid_inverse_and_reflected_cells χ a b H m).2.1 hm⟩
  · have hp' : χ⁻¹.IsPrimitive := by
      change χ⁻¹.conductor=d
      rw [DirichletCharacter.conductor_inv]
      exact hp
    obtain ⟨m,hm⟩ := checks χ⁻¹ hp' (inv_ne_one.mpr hn) good k
    have he := (GRH.dirichlet_grid_inverse_and_reflected_cells χ⁻¹ a b H m).2.1 hm
    exact ⟨m,(GRH.dirichlet_grid_inverse_and_reflected_cells χ a b H m).1.1 he⟩
