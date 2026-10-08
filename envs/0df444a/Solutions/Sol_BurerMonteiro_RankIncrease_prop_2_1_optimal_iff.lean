-- Prove2me | solution 1 for BurerMonteiro.RankIncrease.prop_2_1_optimal_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T04:08:53.714163+00:00
-- url     : https://prove2.me/submissions/b24b04c4-8f5f-4edc-8f68-b2be9a5152a0

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_BurerMonteiro_RankIncrease_Nr

open Matrix
open scoped Matrix.Norms.Frobenius

open scoped MatrixOrder in
lemma bm14a_trace_mul_nonneg {n : ℕ} {X S : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef)
    (hS : S.PosSemidef) : 0 ≤ (X * S).trace := by
  have key : ∀ R : Matrix (Fin n) (Fin n) ℝ, Rᴴ = R → 0 ≤ (R * R * S).trace := by
    intro R hH
    have h := (hS.mul_mul_conjTranspose_same R).trace_nonneg
    rw [hH] at h
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
    exact h
  have hR : CFC.sqrt X * CFC.sqrt X = X := CFC.sqrt_mul_sqrt_self X hX.nonneg
  have hH : (CFC.sqrt X)ᴴ = CFC.sqrt X := (CFC.sqrt_nonneg X).posSemidef.isHermitian
  rw [← hR]
  exact key _ hH

open BurerMonteiro.RankIncrease in
lemma bm14a_gap {n m : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (X S : Matrix (Fin n) (Fin n) ℝ) (y : Fin m → ℝ) (hX : IsPrimalFeasible A b X)
    (hSy : IsDualFeasible C A S y) : frob X S = frob C X - b ⬝ᵥ y := by
  obtain ⟨hXp, hXA⟩ := hX
  obtain ⟨hS, -⟩ := hSy
  have h1 : frob X S = frob S X := by
    unfold frob
    rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [h1, hS]
  unfold frob slack at *
  simp only [Matrix.transpose_sub, Matrix.transpose_sum, Matrix.transpose_smul, Matrix.sub_mul,
    Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_sum, Matrix.trace_smul,
    hXA, dotProduct, smul_eq_mul]
  ring_nf
  simp [mul_comm]

open BurerMonteiro.RankIncrease in
lemma bm14a_gap_nonneg {n m : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (X S : Matrix (Fin n) (Fin n) ℝ) (y : Fin m → ℝ) (hX : IsPrimalFeasible A b X)
    (hSy : IsDualFeasible C A S y) : b ⬝ᵥ y ≤ frob C X := by
  have h := bm14a_gap C A b X S y hX hSy
  have h2 : 0 ≤ frob X S := by
    unfold frob
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, hX.1.isHermitian.eq]
    exact bm14a_trace_mul_nonneg hX.1 hSy.2
  linarith

open BurerMonteiro.RankIncrease in
theorem solution {n m : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) (hC : C.IsSymm)
    (hA : ∀ i, (A i).IsSymm) (hsa : StandingAssumptions C A b)
    (X S : Matrix (Fin n) (Fin n) ℝ) (y : Fin m → ℝ) (hX : IsPrimalFeasible A b X)
    (hSy : IsDualFeasible C A S y) :
    (IsPrimalOptimal C A b X ∧ IsDualOptimal C A b S y) ↔ frob X S = 0 := by
  rw [bm14a_gap C A b X S y hX hSy]
  constructor
  · rintro ⟨⟨-, hXo⟩, ⟨-, hyo⟩⟩
    obtain ⟨-, X', S', y', hX', hSy', heq⟩ := hsa
    have h1 := hXo X' hX'
    have h2 := hyo S' y' hSy'
    have h3 := bm14a_gap_nonneg C A b X S y hX hSy
    linarith
  · intro h
    refine ⟨⟨hX, fun X' hX' => ?_⟩, ⟨hSy, fun S' y' hSy' => ?_⟩⟩
    · have := bm14a_gap_nonneg C A b X' S y hX' hSy
      linarith
    · have := bm14a_gap_nonneg C A b X S' y' hX hSy'
      linarith
