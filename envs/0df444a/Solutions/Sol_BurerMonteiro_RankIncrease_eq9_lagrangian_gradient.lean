-- Prove2me | solution 1 for BurerMonteiro.RankIncrease.eq9_lagrangian_gradient
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T03:44:30.361536+00:00
-- url     : https://prove2.me/submissions/9c89f6d1-405f-4c91-a340-c22d0bfc4e75

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_BurerMonteiro_RankIncrease_Nr

set_option autoImplicit false

open Matrix
open scoped Matrix.Norms.Frobenius

open BurerMonteiro.RankIncrease in
theorem bm71555_lagr_eq {n m r : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) (R : Matrix (Fin n) (Fin r) ℝ)
    (y : Fin m → ℝ) :
    lagrangian C A b R y = frob (slack C A y) (R * Rᵀ) + ∑ i, y i * b i := by
  simp only [lagrangian, frob, slack, transpose_sub, transpose_sum, transpose_smul, sub_mul,
    Finset.sum_mul, trace_sub, trace_sum, smul_mul, trace_smul, mul_sub, Finset.sum_sub_distrib,
    smul_eq_mul]
  ring

open BurerMonteiro.RankIncrease in
/-- the bilinear form `(X, Y) ↦ S • (X Yᵀ)` -/
noncomputable def bm71555_bil {n r : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin r) ℝ →L[ℝ] Matrix (Fin n) (Fin r) ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
        (Matrix (Fin n) (Fin r) ℝ →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (Matrix (Fin n) (Fin r) ℝ →L[ℝ] ℝ)).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun X Y : Matrix (Fin n) (Fin r) ℝ => frob S (X * Yᵀ))
        (by intro X X' Y; simp [frob, Matrix.add_mul, Matrix.mul_add, trace_add])
        (by intro c X Y; simp [frob, trace_smul])
        (by intro X Y Y'; simp [frob, Matrix.mul_add, transpose_add, trace_add])
        (by intro c X Y; simp [frob, transpose_smul, trace_smul]))

open BurerMonteiro.RankIncrease in
theorem bm71555_bil_apply {n r : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (X Y : Matrix (Fin n) (Fin r) ℝ) : bm71555_bil S X Y = frob S (X * Yᵀ) := rfl

open BurerMonteiro.RankIncrease in
theorem solution {n m : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) (hC : C.IsSymm)
    (hA : ∀ i, (A i).IsSymm) {r : ℕ} (hr0 : 0 < r) (hrn : r ≤ n)
    (R : Matrix (Fin n) (Fin r) ℝ) (y : Fin m → ℝ) :
    HasFDerivAt (fun R' : Matrix (Fin n) (Fin r) ℝ => lagrangian C A b R' y)
      (frobCLM ((2 : ℝ) • (slack C A y * R))) R := by
  set S := slack C A y with hSdef
  have hS : Sᵀ = S := by
    rw [hSdef]
    simp only [slack, transpose_sub, transpose_sum, transpose_smul]
    rw [hC.eq]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by rw [(hA i).eq])
  have hB := (bm71555_bil (r := r) S).hasFDerivAt_of_bilinear (hasFDerivAt_id R)
    (hasFDerivAt_id R)
  have hF := hB.add_const (∑ i, y i * b i)
  have hfun : (fun R' : Matrix (Fin n) (Fin r) ℝ => lagrangian C A b R' y) =
      fun R' => bm71555_bil S (id R') (id R') + ∑ i, y i * b i := by
    funext R'
    rw [bm71555_lagr_eq]
    rfl
  rw [hfun]
  refine HasFDerivAt.congr_fderiv hF ?_
  apply ContinuousLinearMap.ext
  intro D
  show frob S (R * Dᵀ) + frob S (D * Rᵀ) = frob ((2 : ℝ) • (S * R)) D
  symm
  simp only [frob, transpose_smul, transpose_mul, hS, Matrix.smul_mul, trace_smul, smul_eq_mul]
  have h1 : (S * (R * Dᵀ)).trace = (Rᵀ * S * D).trace := by
    rw [← trace_transpose (S * (R * Dᵀ))]
    simp only [transpose_mul, transpose_transpose, hS]
    exact (Matrix.trace_mul_cycle _ _ _).symm
  have h2 : (S * (D * Rᵀ)).trace = (Rᵀ * S * D).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  rw [h1, h2]
  ring
