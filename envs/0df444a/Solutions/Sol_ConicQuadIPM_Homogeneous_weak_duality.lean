-- Prove2me | solution 1 for ConicQuadIPM.Homogeneous.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:49:14.572+00:00
-- url     : https://prove2.me/submissions/e2e86ec7-07d2-4358-b62d-7f73c26e99a9

import Mathlib
import Definitions.Def_ConicQuadIPM_Homogeneous_Setting
open Matrix ConicQuadIPM.Homogeneous

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) (hK : IsPointedClosedConvexCone K)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ)
    (hx : PrimalFeasible A b K x) (hys : DualFeasible A c K y s) :
    c ⬝ᵥ x - b ⬝ᵥ y = x ⬝ᵥ s ∧ 0 ≤ x ⬝ᵥ s := by
  obtain ⟨hAx, hxK⟩ := hx
  obtain ⟨heq, hs⟩ := hys
  have hn : 0 ≤ x ⬝ᵥ s := by simpa [dotProduct_comm] using hs x hxK
  have ht : (Aᵀ *ᵥ y) ⬝ᵥ x = b ⬝ᵥ y := by
    rw [dotProduct_comm, dotProduct_mulVec, vecMul_transpose, dotProduct_comm, hAx]
    exact dotProduct_comm y b
  constructor
  · rw [← heq, add_dotProduct, ht, dotProduct_comm s x]
    ring
  · exact hn

#print axioms solution
