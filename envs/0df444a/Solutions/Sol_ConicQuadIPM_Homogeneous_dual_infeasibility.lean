-- Prove2me | solution 1 for ConicQuadIPM.Homogeneous.dual_infeasibility
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:07:43.620453+00:00
-- url     : https://prove2.me/submissions/5a1e1ae8-1b6c-471b-8f86-b1e757bc85c9

import Mathlib
import Definitions.Def_ConicQuadIPM_Homogeneous_Setting
open Matrix ConicQuadIPM.Homogeneous

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) (hK : IsPointedClosedConvexCone K)
    (hcert : ∃ x : Fin n → ℝ, x ∈ K ∧ A *ᵥ x = 0 ∧ c ⬝ᵥ x < 0) :
    DualInfeasible A c K := by
  rintro ⟨y, s, heq, hs⟩
  obtain ⟨x, hx, hAx, hneg⟩ := hcert
  have hp := hs x hx
  have hz : (Aᵀ *ᵥ y) ⬝ᵥ x = 0 := by
    rw [dotProduct_comm, dotProduct_mulVec, vecMul_transpose, dotProduct_comm, hAx, dotProduct_zero]
  rw [← heq, add_dotProduct, hz, zero_add] at hneg
  exact (not_lt_of_ge hp) hneg

#print axioms solution
