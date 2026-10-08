-- Prove2me | solution 1 for ConicQuadIPM.Homogeneous.primal_infeasibility
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:49:13.116673+00:00
-- url     : https://prove2.me/submissions/f8891df5-bf8c-4a4d-bd1d-615c50cf2792

import Mathlib
import Definitions.Def_ConicQuadIPM_Homogeneous_Setting
open Matrix ConicQuadIPM.Homogeneous

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (K : Set (Fin n → ℝ)) (hK : IsPointedClosedConvexCone K)
    (hcert : ∃ (y : Fin m → ℝ) (s : Fin n → ℝ),
      s ∈ dualCone K ∧ Aᵀ *ᵥ y + s = 0 ∧ 0 < b ⬝ᵥ y) :
    PrimalInfeasible A b K := by
  rintro ⟨x, hAx, hx⟩
  obtain ⟨y, s, hs, heq, hp⟩ := hcert
  have hn := hs x hx
  have hd := congrArg (fun v => v ⬝ᵥ x) heq
  have ht : (Aᵀ *ᵥ y) ⬝ᵥ x = b ⬝ᵥ y := by
    rw [dotProduct_comm, dotProduct_mulVec, vecMul_transpose, dotProduct_comm, hAx]
    exact dotProduct_comm y b
  simp only [add_dotProduct, zero_dotProduct] at hd
  rw [ht] at hd
  linarith

#print axioms solution
