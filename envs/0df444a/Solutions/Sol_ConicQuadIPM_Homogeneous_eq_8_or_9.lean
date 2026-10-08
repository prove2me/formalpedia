-- Prove2me | solution 1 for ConicQuadIPM.Homogeneous.eq_8_or_9
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:49:16.205028+00:00
-- url     : https://prove2.me/submissions/12bfe74a-592f-4d7b-9bd7-2af3c84137dd

import Mathlib
import Definitions.Def_ConicQuadIPM_Homogeneous_Setting
open Matrix ConicQuadIPM.Homogeneous

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) (hK : IsPointedClosedConvexCone K)
    (x : Fin n → ℝ) (τ : ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) (κ : ℝ)
    (h : HomFeasible A b c K x τ y s κ) (hκ : 0 < κ) :
    0 < b ⬝ᵥ y ∨ c ⬝ᵥ x < 0 := by
  have hg := h.2.2.1
  by_cases hb : 0 < b ⬝ᵥ y
  · exact Or.inl hb
  · right
    linarith

#print axioms solution

