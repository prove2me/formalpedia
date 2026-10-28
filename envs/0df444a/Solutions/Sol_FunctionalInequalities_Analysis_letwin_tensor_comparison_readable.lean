-- Prove2me | solution 1 for FunctionalInequalities.Analysis.letwin_tensor_comparison_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:41:01.504049+00:00
-- url     : https://prove2.me/submissions/6230f8c9-2ab4-4405-ad30-6cd4937c381b

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Trace_Energy
import Theorems.Thm_FunctionalInequalities_Analysis_letwin_tensor_trace_identity_readable
import Theorems.Thm_FunctionalInequalities_Analysis_letwin_trace_weighted_slices_readable

open Matrix
section TensorComparison
private lemma FunctionalInequalities.Analysis.letwin_real_transpose {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) :
    Mᵀ = M := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hM.eq
open scoped MatrixOrder in
private lemma FunctionalInequalities.Analysis.letwin_psd_factor {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ, A = Pᵀ * P := by
  classical
  obtain ⟨P, hP⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  refine ⟨P, ?_⟩
  simpa only [Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using hP
private lemma FunctionalInequalities.Analysis.letwin_trace_square_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (A * A).trace ≤ (A * Aᵀ).trace := by
  classical
  change (∑ i, ∑ j, A i j * A j i) ≤ ∑ i, ∑ j, A i j * A i j
  have hswap :
      (∑ i, ∑ j, A j i * A j i) = ∑ i, ∑ j, A i j * A i j := by
    rw [Finset.sum_comm]
  have h :
      2 * (∑ i, ∑ j, A i j * A j i) ≤
        (∑ i, ∑ j, A i j * A i j) + (∑ i, ∑ j, A j i * A j i) := by
    calc
      2 * (∑ i, ∑ j, A i j * A j i) =
          ∑ i, ∑ j, 2 * (A i j * A j i) := by
        simp only [Finset.mul_sum]
      _ ≤ ∑ i, ∑ j, (A i j * A i j + A j i * A j i) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        nlinarith only [sq_nonneg (A i j - A j i)]
      _ = (∑ i, ∑ j, A i j * A i j) +
          (∑ i, ∑ j, A j i * A j i) := by
        simp only [Finset.sum_add_distrib]
  rw [hswap] at h
  linarith
private lemma FunctionalInequalities.Analysis.letwin_trace_sandwich {n : ℕ}
    (P X : Matrix (Fin n) (Fin n) ℝ) :
    (P * X * Pᵀ).trace = (X * (Pᵀ * P)).trace := by
  calc
    (P * X * Pᵀ).trace = (P * (X * Pᵀ)).trace := by
      rw [Matrix.mul_assoc]
    _ = ((X * Pᵀ) * P).trace := Matrix.trace_mul_comm _ _
    _ = (X * (Pᵀ * P)).trace := by
      rw [Matrix.mul_assoc]
private lemma FunctionalInequalities.Analysis.letwin_trace_sandwich_product {n : ℕ}
    (P X Y : Matrix (Fin n) (Fin n) ℝ) :
    ((P * X * Pᵀ) * (P * Y * Pᵀ)).trace =
      ((X * (Pᵀ * P)) * (Y * (Pᵀ * P))).trace := by
  calc
    ((P * X * Pᵀ) * (P * Y * Pᵀ)).trace =
        (P * (X * (Pᵀ * P) * Y) * Pᵀ).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((X * (Pᵀ * P) * Y) * (Pᵀ * P)).trace := by
      simpa only [Matrix.mul_assoc] using
        (letwin_trace_sandwich P (X * (Pᵀ * P) * Y))
    _ = ((X * (Pᵀ * P)) * (Y * (Pᵀ * P))).trace := by
      simp only [Matrix.mul_assoc]
private lemma FunctionalInequalities.Analysis.letwin_slice_comparison {n : ℕ}
    (H B S P : Matrix (Fin n) (Fin n) ℝ)
    (hH : Hᵀ = H) (hB : Bᵀ = B) (hS : Sᵀ = S)
    (hcancel : H * (Pᵀ * P) = 1) :
    (B * S * B * S).trace ≤
      ((B * H * B) * S * (Pᵀ * P) * S).trace := by
  have hx : (S * B * H) * (Pᵀ * P) = S * B := by
    calc
      (S * B * H) * (Pᵀ * P) = (S * B) * (H * (Pᵀ * P)) := by
        rw [Matrix.mul_assoc]
      _ = S * B := by
        rw [hcancel, Matrix.mul_one]
  have ht :
      (P * (S * B * H) * Pᵀ)ᵀ = P * (H * B * S) * Pᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
      hH, hB, hS, Matrix.mul_assoc]
  have h := letwin_trace_square_le (P * (S * B * H) * Pᵀ)
  rw [ht] at h
  simp only [letwin_trace_sandwich_product, hx] at h
  calc
    (B * S * B * S).trace = (S * (B * S * B)).trace :=
      Matrix.trace_mul_comm _ _
    _ = ((S * B) * (S * B)).trace := by
      simp only [Matrix.mul_assoc]
    _ ≤ ((S * B) * ((H * B * S) * (Pᵀ * P))).trace := h
    _ = (S * (B * H * B * S * (Pᵀ * P))).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((B * H * B) * S * (Pᵀ * P) * S).trace :=
      Matrix.trace_mul_comm _ _
/-- **Letwin's tensor comparison** (Letwin arXiv:2607.24164v1, (2.12), p. 10), in arbitrary
coordinates: for a positive definite `H` (the Hessian `∇²φ(y)`), a symmetric `B` and a fully
symmetric 3-tensor `T` (the third derivatives `∂_{abi}φ(y)`), with slices `(T_a)_{ij} = T a i j`,
`∑_{a,b} (H⁻¹)_{ab} tr(B T_a B T_b) ≤ ∑_{i,j} (B H B)_{ij} ∑_{a,b,c,d} (H⁻¹)_{ac} (H⁻¹)_{bd} T_{abi} T_{cdj}`. -/
theorem solution {n : ℕ} (H B : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef)
    (hB : B.IsHermitian) (T : Fin n → Fin n → Fin n → ℝ)
    (hT₁ : ∀ a b c, T a b c = T b a c) (hT₂ : ∀ a b c, T a b c = T a c b) :
    ∑ a, ∑ b, H⁻¹ a b * (B * Matrix.of (fun i j => T a i j) * B *
        Matrix.of (fun i j => T b i j)).trace ≤
      ∑ i, ∑ j, (B * H * B) i j *
        ∑ a, ∑ b, ∑ c, ∑ d, H⁻¹ a c * H⁻¹ b d * T a b i * T c d j := by
  classical
  have hHt : Hᵀ = H := FunctionalInequalities.Analysis.letwin_real_transpose H hH.isHermitian
  have hBt : Bᵀ = B := FunctionalInequalities.Analysis.letwin_real_transpose B hB
  have hInv : (H⁻¹).PosSemidef := hH.inv.posSemidef
  obtain ⟨P, hP⟩ := FunctionalInequalities.Analysis.letwin_psd_factor (H⁻¹) hInv
  have hcancel : H * (Pᵀ * P) = 1 := by
    rw [← hP]
    exact Matrix.mul_nonsing_inv H
      (isUnit_iff_ne_zero.mpr (ne_of_gt hH.det_pos))
  let V : Fin n → Matrix (Fin n) (Fin n) ℝ :=
    fun a => Matrix.of (fun i j => T a i j)
  let S : Fin n → Matrix (Fin n) (Fin n) ℝ :=
    fun k => ∑ a, (P k a) • V a
  have hSt (k : Fin n) : (S k)ᵀ = S k := by
    ext i j
    change (∑ a, (P k a) • V a) j i = (∑ a, (P k a) • V a) i j
    simp only [Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro a _
    change P k a * T a j i = P k a * T a i j
    congr 1
    calc
      T a j i = T j a i := hT₁ a j i
      _ = T j i a := hT₂ j a i
      _ = T i j a := hT₁ j i a
      _ = T i a j := hT₂ i j a
      _ = T a i j := hT₁ i a j
  have hMt : (B * H * B)ᵀ = B * H * B := by
    simp only [Matrix.transpose_mul, hBt, hHt, Matrix.mul_assoc]
  change (∑ a, ∑ b, H⁻¹ a b * (B * V a * B * V b).trace) ≤ _
  calc
    (∑ a, ∑ b, H⁻¹ a b * (B * V a * B * V b).trace) =
        ∑ k, (B * S k * B * S k).trace := by
      symm
      simpa only [S, hP] using FunctionalInequalities.Analysis.letwin_trace_weighted_slices_readable P B B V
    _ ≤ ∑ k, ((B * H * B) * S k * (Pᵀ * P) * S k).trace := by
      apply Finset.sum_le_sum
      intro k _
      exact FunctionalInequalities.Analysis.letwin_slice_comparison H B (S k) P hHt hBt (hSt k) hcancel
    _ = ∑ a, ∑ c, (Pᵀ * P) a c *
        ((B * H * B) * V a * (Pᵀ * P) * V c).trace :=
      FunctionalInequalities.Analysis.letwin_trace_weighted_slices_readable P (B * H * B) (Pᵀ * P) V
    _ = ∑ i, ∑ j, (B * H * B) i j *
        ∑ a, ∑ b, ∑ c, ∑ d, H⁻¹ a c * H⁻¹ b d * T a b i * T c d j := by
      simpa only [V, hP] using
        (FunctionalInequalities.Analysis.letwin_tensor_trace_identity_readable (Pᵀ * P) (B * H * B) hMt T hT₂)
