-- Prove2me | solution 1 for EulerSparsify.lemma_5_6
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T12:53:18.822802+00:00
-- url     : https://prove2.me/submissions/1a0948ac-04f3-4d55-8416-1c02c50e0c83

import Mathlib

open Matrix
open scoped Matrix

namespace EulerSparsify

lemma sum_univ_prod {α β : Type*} [Fintype α] [Fintype β] {M : Type*} [AddCommMonoid M]
    (f : α × β → M) : ∑ x, f x = ∑ a, ∑ b, f (a, b) := by
  rw [← Finset.univ_product_univ]
  exact Finset.sum_product _ _ _

/-- Expansion of `∑ i, (∑ j, R j i • A j) * (∑ j, R j i • A j)ᵀ`
as `∑ j k, (R * Rᵀ) j k • (A j * (A k)ᵀ)`. -/
lemma sum_expand {m n : ℕ} (R : Matrix (Fin m) (Fin m) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, (∑ j, R j i • A j) * (∑ j, R j i • A j).transpose)
      = ∑ j, ∑ k, (R * R.transpose) j k • (A j * (A k).transpose) := by
  have step : ∀ i, (∑ j, R j i • A j) * (∑ j, R j i • A j).transpose
      = ∑ j, ∑ k, (R j i * R k i) • (A j * (A k).transpose) := by
    intro i
    rw [Matrix.transpose_sum]
    simp only [Matrix.transpose_smul, Matrix.transpose_transpose]
    rw [Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show (∑ i, (∑ j, R j i • A j) * (∑ j, R j i • A j).transpose)
      = ∑ i, ∑ j, ∑ k, (R j i * R k i) • (A j * (A k).transpose) from
    Finset.sum_congr rfl (fun i _ => step i)]
  calc ∑ i, ∑ j, ∑ k, (R j i * R k i) • (A j * (A k).transpose)
      = ∑ j, ∑ i, ∑ k, (R j i * R k i) • (A j * (A k).transpose) := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, (R j i * R k i) • (A j * (A k).transpose) := by
        apply Finset.sum_congr rfl
        intro j _
        exact Finset.sum_comm
    _ = ∑ j, ∑ k, (∑ i, R j i * R k i) • (A j * (A k).transpose) := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_smul]
    _ = ∑ j, ∑ k, (R * R.transpose) j k • (A j * (A k).transpose) := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        simp [Matrix.mul_apply, Matrix.transpose_apply]

/-- If `M` is positive semidefinite then `∑ j k, M j k • (A j * (A k)ᵀ)` is. -/
lemma psd_double_sum {m n : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (hM : M.PosSemidef)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    (∑ j, ∑ k, M j k • (A j * (A k).transpose)).PosSemidef := by
  classical
  set V : Matrix (Fin n) (Fin m × Fin n) ℝ := fun p q => A q.1 p q.2 with hV
  set K : Matrix (Fin m × Fin n) (Fin m × Fin n) ℝ :=
    kroneckerMap (fun a b : ℝ => a * b) M (1 : Matrix (Fin n) (Fin n) ℝ) with hK
  have hKpsd : K.PosSemidef := by
    rw [hK]
    exact PosSemidef.kronecker hM PosSemidef.one
  have hVKV : (V * K * Vᴴ).PosSemidef := hKpsd.mul_mul_conjTranspose_same V
  have hHerm : Vᴴ = Vᵀ := by
    ext p q
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial]
  rw [hHerm] at hVKV
  have hid : (∑ j, ∑ k, M j k • (A j * (A k).transpose)) = V * K * Vᵀ := by
    ext p q
    have hL : (∑ j, ∑ k, M j k • (A j * (A k).transpose)) p q
        = ∑ j, ∑ k, ∑ r, M j k * (A j p r * A k q r) := by
      simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
    have hR : (V * K * Vᵀ) p q = ∑ j, ∑ k, ∑ r, M j k * (A j p r * A k q r) := by
      have hstep1 : (V * K * Vᵀ) p q
          = ∑ a : Fin m × Fin n, (∑ b : Fin m × Fin n, V p b * K b a) * V q a := by
        rw [Matrix.mul_apply]
        simp only [Matrix.mul_apply, Matrix.transpose_apply]
      rw [hstep1]
      simp only [sum_univ_prod]
      simp only [hV, hK, Matrix.kroneckerMap_apply, Matrix.one_apply]
      simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      calc ∑ x, ∑ y, (∑ c, A c p y * M c x) * A x q y
          = ∑ x, ∑ y, ∑ c, (A c p y * M c x) * A x q y := by
              apply Finset.sum_congr rfl
              intro x _
              apply Finset.sum_congr rfl
              intro y _
              rw [Finset.sum_mul]
        _ = ∑ x, ∑ c, ∑ y, (A c p y * M c x) * A x q y := by
              apply Finset.sum_congr rfl
              intro x _
              exact Finset.sum_comm
        _ = ∑ c, ∑ x, ∑ y, (A c p y * M c x) * A x q y := Finset.sum_comm
        _ = ∑ j, ∑ k, ∑ r, M j k * (A j p r * A k q r) := by
              apply Finset.sum_congr rfl
              intro j _
              apply Finset.sum_congr rfl
              intro k _
              apply Finset.sum_congr rfl
              intro r _
              ring
    rw [hL, hR]
  rw [hid]
  exact hVKV

end EulerSparsify

/-- Lemma 5.6: PPᵀ ⪯ QQᵀ implies ∑ Ĉ_i Ĉ_iᵀ ⪯ ∑ Â_i Â_iᵀ. -/
theorem solution {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (P Q : Matrix (Fin m) (Fin m) ℝ) (hPQ : (Q * Q.transpose - P * P.transpose).PosSemidef) :
    ((∑ i, (∑ j, Q j i • A j) * (∑ j, Q j i • A j).transpose) -
      ∑ i, (∑ j, P j i • A j) * (∑ j, P j i • A j).transpose).PosSemidef := by
  rw [EulerSparsify.sum_expand Q A, EulerSparsify.sum_expand P A]
  have hsub : (∑ j, ∑ k, (Q * Q.transpose) j k • (A j * (A k).transpose))
      - (∑ j, ∑ k, (P * P.transpose) j k • (A j * (A k).transpose))
      = ∑ j, ∑ k, ((Q * Q.transpose - P * P.transpose) j k) • (A j * (A k).transpose) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [Matrix.sub_apply, sub_smul]
  rw [hsub]
  exact EulerSparsify.psd_double_sum _ hPQ A
