-- Prove2me | solution 1 for FriedCrossing.Derived.semisimple_of_states
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:04:15.696797+00:00
-- url     : https://prove2.me/submissions/6f2a1a8b-2f83-4873-ae7a-9ff4369650ea

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_FriedCrossing_Derived_matrix_scalar_of_two_eigenvectors

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Derived
namespace FriedCrossing.Derived
theorem _root_.solution (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (sStar : ℝ → ℝ)
    (hstates : ∀ θ, ∃ v₁ v₂ : Fin 2 → ℝ, LinearIndependent ℝ ![v₁, v₂] ∧
      M θ 0 *ᵥ v₁ = sStar θ • v₁ ∧ M θ 0 *ᵥ v₂ = sStar θ • v₂) :
    ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ) := fun θ => by
  obtain ⟨v₁, v₂, hind, h₁, h₂⟩ := hstates θ
  exact matrix_scalar_of_two_eigenvectors _ _ _ _ hind h₁ h₂
end FriedCrossing.Derived
