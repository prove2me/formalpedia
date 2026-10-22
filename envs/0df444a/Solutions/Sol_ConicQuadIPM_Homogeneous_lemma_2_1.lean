-- Prove2me | solution 1 for ConicQuadIPM.Homogeneous.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:40:55.936278+00:00
-- url     : https://prove2.me/submissions/34faa5db-6030-472d-a25a-7305e0f1e289

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

theorem X_dot_tr {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ) :
    x ⬝ᵥ (Aᵀ *ᵥ y) = (A *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) (hK : IsPointedClosedConvexCone K)
    (x : Fin n → ℝ) (τ : ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) (κ : ℝ)
    (h : HomFeasible A b c K x τ y s κ) :
    x ⬝ᵥ s + τ * κ = 0 ∧
    (0 < τ → PrimalOptimal A b c K (τ⁻¹ • x) ∧ DualOptimal A b c K (τ⁻¹ • y) (τ⁻¹ • s)) ∧
    (0 < κ → (0 < b ⬝ᵥ y ∨ c ⬝ᵥ x < 0) ∧ (0 < b ⬝ᵥ y → PrimalInfeasible A b K) ∧
      (c ⬝ᵥ x < 0 → DualInfeasible A c K)) := by
  obtain ⟨k1, k2, k3⟩ := X_hom_key A b c K x τ y s κ h
  obtain ⟨h1, h2, h3, ⟨hx, hτ⟩, ⟨hs, hκ⟩⟩ := h
  have e1 : A *ᵥ x = τ • b := sub_eq_zero.1 h1
  have e2 : Aᵀ *ᵥ y + s = τ • c := sub_eq_zero.1 h2
  have e3 : b ⬝ᵥ y = c ⬝ᵥ x + κ := by linarith
  refine ⟨k1, ?_, ?_⟩
  · intro hτpos
    have hκ0 : κ = 0 := by
      have : τ * κ = 0 := by linarith
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd h0 hτpos.ne'
      · exact h0
    have hbc : b ⬝ᵥ y = c ⬝ᵥ x := by rw [e3, hκ0]; ring
    have hsc : s = τ • c - Aᵀ *ᵥ y := by rw [← e2]; abel
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩
    · rw [Matrix.mulVec_smul, e1, smul_smul, inv_mul_cancel₀ hτpos.ne', one_smul]
    · exact hK.2.2.1 x hx τ⁻¹ (inv_nonneg.2 hτ)
    · rintro x' ⟨hx'1, hx'K⟩
      have hs'x : 0 ≤ s ⬝ᵥ x' := hs x' hx'K
      have hτc : τ * (c ⬝ᵥ x') = b ⬝ᵥ y + s ⬝ᵥ x' := by
        have h' : (τ • c) ⬝ᵥ x' = (Aᵀ *ᵥ y + s) ⬝ᵥ x' := by rw [e2]
        rw [smul_dotProduct, add_dotProduct, dotProduct_comm (Aᵀ *ᵥ y) x', X_dot_tr, hx'1,
          smul_eq_mul] at h'
        exact h'
      rw [dotProduct_smul, smul_eq_mul]
      calc τ⁻¹ * (c ⬝ᵥ x) = τ⁻¹ * (b ⬝ᵥ y) := by rw [hbc]
        _ ≤ τ⁻¹ * (τ * (c ⬝ᵥ x')) :=
            mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hτ)
        _ = c ⬝ᵥ x' := by field_simp
    · rw [Matrix.mulVec_smul, ← smul_add, e2, smul_smul, inv_mul_cancel₀ hτpos.ne', one_smul]
    · intro z hz
      rw [smul_dotProduct]
      exact mul_nonneg (inv_nonneg.2 hτ) (hs z hz)
    · rintro y' s' ⟨hy's', hs'K⟩
      rw [dotProduct_smul, smul_eq_mul]
      have hcs : Aᵀ *ᵥ y' = c - s' := eq_sub_of_add_eq hy's'
      have hxs' : 0 ≤ x ⬝ᵥ s' := by rw [dotProduct_comm]; exact hs'K x hx
      have hτy : τ * (b ⬝ᵥ y') = c ⬝ᵥ x - x ⬝ᵥ s' := by
        have h' : (A *ᵥ x) ⬝ᵥ y' = x ⬝ᵥ (Aᵀ *ᵥ y') := (X_dot_tr A x y').symm
        rw [e1, smul_dotProduct, smul_eq_mul, hcs, dotProduct_sub, dotProduct_comm x c] at h'
        exact h'
      calc b ⬝ᵥ y' = τ⁻¹ * (τ * (b ⬝ᵥ y')) := by field_simp
        _ ≤ τ⁻¹ * (b ⬝ᵥ y) :=
            mul_le_mul_of_nonneg_left (by rw [hbc]; linarith) (inv_nonneg.2 hτ)
  · intro hκpos
    have hτ0 : τ = 0 := by
      have : τ * κ = 0 := by linarith
      rcases mul_eq_zero.1 this with h0 | h0
      · exact h0
      · exact absurd h0 hκpos.ne'
    have hAx : A *ᵥ x = 0 := by simpa [hτ0] using e1
    have hAy : Aᵀ *ᵥ y + s = 0 := by simpa [hτ0] using e2
    refine ⟨?_, ?_, ?_⟩
    · by_contra hcon
      rw [not_or, not_lt, not_lt] at hcon
      linarith [hcon.1, hcon.2]
    · intro hby ⟨x', hx'1, hx'K⟩
      have : b ⬝ᵥ y = -(s ⬝ᵥ x') := by
        have hs2 : Aᵀ *ᵥ y = -s := eq_neg_of_add_eq_zero_left hAy
        have hh : b ⬝ᵥ y = x' ⬝ᵥ (Aᵀ *ᵥ y) := by rw [X_dot_tr, hx'1]
        rw [hh, hs2, dotProduct_neg, dotProduct_comm]
      have := hs x' hx'K
      linarith
    · intro hcx ⟨y', s', hy's', hs'K⟩
      have : c ⬝ᵥ x = s' ⬝ᵥ x := by
        rw [← hy's', add_dotProduct, dotProduct_comm (Aᵀ *ᵥ y') x, X_dot_tr, hAx]
        simp
      have := hs'K x hx
      linarith
