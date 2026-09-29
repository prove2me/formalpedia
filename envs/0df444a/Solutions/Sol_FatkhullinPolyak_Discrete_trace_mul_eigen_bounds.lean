-- Prove2me | solution 1 for FatkhullinPolyak.Discrete.trace_mul_eigen_bounds
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:14:18.796709+00:00
-- url     : https://prove2.me/submissions/1533dcc6-9ef1-4cde-be6d-9c368ccb5c2c

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_Matrix

namespace FatkhullinPolyak.Discrete

theorem aux_tmeb_decomp {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (hB : B.PosSemidef) :
    ∃ c : Fin n → ℝ, (∀ i, 0 ≤ c i) ∧ Matrix.trace B = ∑ i, c i ∧
      Matrix.trace (A * B) = ∑ i, hA.eigenvalues i * c i := by
  set U : Matrix (Fin n) (Fin n) ℝ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  set C := star U * B * U with hC
  have hCpsd : C.PosSemidef := by
    have := hB.conjTranspose_mul_mul_same U
    simpa [hC, Matrix.star_eq_conjTranspose] using this
  refine ⟨fun i => C i i, fun i => hCpsd.diag_nonneg, ?_, ?_⟩
  · have h1 : Matrix.trace C = Matrix.trace B := by
      rw [hC, Matrix.trace_mul_cycle, hUU', Matrix.one_mul]
    rw [← h1]
    rfl
  · have hspec := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hspec
    have hD : (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) : Matrix (Fin n) (Fin n) ℝ)
        = Matrix.diagonal hA.eigenvalues := by
      congr 1
    rw [hD] at hspec
    have : Matrix.trace (A * B) = Matrix.trace (Matrix.diagonal hA.eigenvalues * C) := by
      conv_lhs => rw [hspec]
      rw [hC]
      simp only [← hU]
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
        Matrix.mul_assoc]
    rw [this, Matrix.trace]
    simp [Matrix.diagonal_mul]

end FatkhullinPolyak.Discrete

open FatkhullinPolyak.Discrete

theorem solution {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    lamMin A * Matrix.trace B ≤ Matrix.trace (A * B) ∧
      Matrix.trace (A * B) ≤ lamMax A * Matrix.trace B := by
  obtain ⟨c, hc0, htr, hAB⟩ := aux_tmeb_decomp A B hA.isHermitian hB
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : Matrix.trace B = 0 := by simp [Matrix.trace]
    have h2 : Matrix.trace (A * B) = 0 := by simp [Matrix.trace]
    rw [h1, h2]; simp
  · have hmin : lamMin A = Finset.univ.inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
        hA.isHermitian.eigenvalues := by
      unfold lamMin; rw [dif_pos hA.isHermitian, dif_pos hn]
    have hmax : lamMax A = Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
        hA.isHermitian.eigenvalues := by
      unfold lamMax; rw [dif_pos hA.isHermitian, dif_pos hn]
    rw [htr, hAB, Finset.mul_sum, Finset.mul_sum]
    constructor
    · apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ (hc0 i)
      rw [hmin]
      exact Finset.inf'_le _ (Finset.mem_univ i)
    · apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ (hc0 i)
      rw [hmax]
      exact Finset.le_sup' _ (Finset.mem_univ i)
