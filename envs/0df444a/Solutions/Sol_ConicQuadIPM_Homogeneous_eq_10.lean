-- Prove2me | solution 1 for ConicQuadIPM.Homogeneous.eq_10
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:38:03.186456+00:00
-- url     : https://prove2.me/submissions/0f64244f-1b0e-48e7-b593-00d371946d14

import Mathlib
import Definitions.Def_ConicQuadIPM_Homogeneous_Setting

set_option autoImplicit false
open Matrix ConicQuadIPM.Homogeneous

theorem X_hom_key {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) (x : Fin n → ℝ) (τ : ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) (κ : ℝ)
    (h : HomFeasible A b c K x τ y s κ) :
    x ⬝ᵥ s + τ * κ = 0 ∧ 0 ≤ x ⬝ᵥ s ∧ 0 ≤ τ * κ := by
  obtain ⟨h1, h2, h3, ⟨hx, hτ⟩, ⟨hs, hκ⟩⟩ := h
  have e1 : A *ᵥ x = τ • b := sub_eq_zero.1 h1
  have e2 : Aᵀ *ᵥ y + s = τ • c := sub_eq_zero.1 h2
  have e3 : b ⬝ᵥ y = c ⬝ᵥ x + κ := by linarith
  have hs' : s = τ • c - Aᵀ *ᵥ y := by rw [← e2]; abel
  have e4 : x ⬝ᵥ (Aᵀ *ᵥ y) = (A *ᵥ x) ⬝ᵥ y := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have e5 : x ⬝ᵥ s = τ * (c ⬝ᵥ x) - τ * (b ⬝ᵥ y) := by
    rw [hs', dotProduct_sub, dotProduct_smul, e4, e1, smul_dotProduct, dotProduct_comm x c]
    simp
  have hnn : 0 ≤ x ⬝ᵥ s := by rw [dotProduct_comm]; exact hs x hx
  refine ⟨?_, hnn, mul_nonneg hτ hκ⟩
  rw [e5, e3]; ring

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) (hK : IsPointedClosedConvexCone K)
    (x : Fin n → ℝ) (τ : ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) (κ : ℝ)
    (h : HomFeasible A b c K x τ y s κ) (hκ : 0 < κ) (h8 : 0 < b ⬝ᵥ y) :
    0 < b ⬝ᵥ y ∧ Aᵀ *ᵥ y + s = 0 ∧ s ∈ dualCone K := by
  obtain ⟨k1, k2, k3⟩ := X_hom_key A b c K x τ y s κ h
  have hτ0 : τ = 0 := by
    have : τ * κ = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · exact h0
    · exact absurd h0 hκ.ne'
  obtain ⟨-, h2, -, -, ⟨hs, -⟩⟩ := h
  refine ⟨h8, ?_, hs⟩
  have := sub_eq_zero.1 h2
  simpa [hτ0] using this
