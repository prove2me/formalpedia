-- Prove2me | solution 1 for ConeLifts.StableSet.blockSlack_not_psdFactorization
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T03:12:31.965107+00:00
-- url     : https://prove2.me/submissions/068bf634-8604-4e44-bc68-a7a919b83341

import Mathlib
import Definitions.Def_ConeLifts_StableSet_HasPSDFactorization

namespace ConeLifts.StableSet.A899

open Matrix

open scoped MatrixOrder in
/-- Two PSD matrices with zero trace pairing multiply to zero. -/
theorem psd_mul_eq_zero_of_trace {k : ℕ} {A B : Matrix (Fin k) (Fin k) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (h : (A * B).trace = 0) : A * B = 0 := by
  obtain ⟨X, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  obtain ⟨Y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  simp only [Matrix.star_eq_conjTranspose] at h ⊢
  have hZ : (X * Yᴴ)ᴴ * (X * Yᴴ) = Y * (Xᴴ * X * Yᴴ) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  have htr : ((X * Yᴴ)ᴴ * (X * Yᴴ)).trace = 0 := by
    rw [hZ, Matrix.trace_mul_comm]
    simpa only [Matrix.mul_assoc] using h
  have hz : X * Yᴴ = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htr
  calc Xᴴ * X * (Yᴴ * Y) = Xᴴ * (X * Yᴴ) * Y := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hz, Matrix.mul_zero, Matrix.zero_mul]

theorem mat_eq_zero_of_mulVec {k : ℕ} {M : Matrix (Fin k) (Fin k) ℝ}
    (h : ∀ w, M *ᵥ w = 0) : M = 0 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro w
  simpa [Matrix.toLin'_apply] using h w

end ConeLifts.StableSet.A899

open ConeLifts.StableSet Matrix in
theorem solution {n : ℕ} (s : Fin n → ℝ) :
    ¬ HasPSDFactorization n
      (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) (0 : Matrix (Fin 1) (Fin n) ℝ)
        (Matrix.of fun (i : Fin n) (_ : Fin 1) => s i) (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  rintro ⟨a, b, ha, hb, hab⟩
  have key : ∀ i j, (a i * b j).trace = 0 → a i * b j = 0 := fun i j h =>
    ConeLifts.StableSet.A899.psd_mul_eq_zero_of_trace (ha i) (hb j) h
  have hne : ∀ j : Fin n, a (Sum.inr j) * b (Sum.inr j) ≠ 0 := by
    intro j h
    have := hab (Sum.inr j) (Sum.inr j)
    rw [h] at this
    simp at this
  have hw : ∀ j : Fin n, ∃ w, (a (Sum.inr j) * b (Sum.inr j)) *ᵥ w ≠ 0 := by
    intro j
    by_contra hc
    simp only [not_exists, ne_eq, not_not] at hc
    exact hne j (ConeLifts.StableSet.A899.mat_eq_zero_of_mulVec hc)
  choose w hw using hw
  set u : Fin n → (Fin n → ℝ) := fun j => b (Sum.inr j) *ᵥ w j with hu
  have hoff : ∀ i j : Fin n, i ≠ j → a (Sum.inr i) * b (Sum.inr j) = 0 := by
    intro i j hij
    apply key
    rw [hab]
    simp [Matrix.one_apply_ne hij]
  have hli : LinearIndependent ℝ u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h2 := congrArg (fun v => a (Sum.inr i) *ᵥ v) hg
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.mulVec_zero] at h2
    rw [Finset.sum_eq_single i] at h2
    · simp only [hu, Matrix.mulVec_mulVec] at h2
      exact (smul_eq_zero.mp h2).resolve_right (hw i)
    · intro j _ hji
      simp only [hu, Matrix.mulVec_mulVec, hoff i j (Ne.symm hji), Matrix.zero_mulVec, smul_zero]
    · simp
  have hspan : Submodule.span ℝ (Set.range u) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp)
  have h0 : ∀ j : Fin n, a (Sum.inl 0) * b (Sum.inr j) = 0 := by
    intro j
    apply key
    rw [hab]
    simp
  have hA0 : a (Sum.inl 0) = 0 := by
    have hker : Submodule.span ℝ (Set.range u) ≤ LinearMap.ker (Matrix.toLin' (a (Sum.inl 0))) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      simp [hu, Matrix.toLin'_apply, Matrix.mulVec_mulVec, h0 j]
    rw [hspan] at hker
    apply ConeLifts.StableSet.A899.mat_eq_zero_of_mulVec
    intro v
    have := hker (Submodule.mem_top (x := v))
    simpa [Matrix.toLin'_apply] using this
  have := hab (Sum.inl 0) (Sum.inl 0)
  rw [hA0] at this
  simp at this
