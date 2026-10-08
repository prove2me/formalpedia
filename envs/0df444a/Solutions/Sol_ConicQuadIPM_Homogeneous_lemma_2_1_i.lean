-- Prove2me | solution 1 for ConicQuadIPM.Homogeneous.lemma_2_1_i
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:49:11.445786+00:00
-- url     : https://prove2.me/submissions/5d19b355-6e6d-4380-bb90-1e09ee4cade4

import Mathlib
import Definitions.Def_ConicQuadIPM_Homogeneous_Setting
open Matrix ConicQuadIPM.Homogeneous

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) (hK : IsPointedClosedConvexCone K)
    (x : Fin n → ℝ) (τ : ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) (κ : ℝ)
    (h : HomFeasible A b c K x τ y s κ) :
    x ⬝ᵥ s + τ * κ = 0 := by
  obtain ⟨hAx, hys, hgap, _⟩ := h
  have hAx' := sub_eq_zero.mp hAx
  have hys' := sub_eq_zero.mp hys
  have hd := congrArg (fun v => v ⬝ᵥ x) hys'
  have ht : (Aᵀ *ᵥ y) ⬝ᵥ x = τ * (b ⬝ᵥ y) := by
    rw [dotProduct_comm, dotProduct_mulVec, vecMul_transpose, dotProduct_comm, hAx',
      dotProduct_smul, dotProduct_comm]
    simp [smul_eq_mul]
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul] at hd
  rw [ht, dotProduct_comm s x] at hd
  nlinarith

#print axioms solution

