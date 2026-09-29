-- Prove2me | solution 2 for ExactSDPDuality.ELSD.prop7_vi
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T01:55:32.972411+00:00
-- url     : https://prove2.me/submissions/03d8afb2-e0a0-46f9-b113-c68569e9197b

import Mathlib
import Definitions.Def_ExactSDPDuality_ELSD_Model

open Matrix
open scoped MatrixOrder
open ExactSDPDuality.ELSD

theorem solution {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    frob A B = 0 ↔ A * B = 0 := by
  have hfrob : frob A B = (A * B).trace := by
    unfold frob
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have := hB.1.apply j i
    simp only [star_trivial] at this
    rw [this]
  constructor
  · intro h0
    rw [hfrob] at h0
    obtain ⟨P, hP⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
    obtain ⟨Q, hQ⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
    rw [Matrix.star_eq_conjTranspose] at hP hQ
    have hX : P * Qᴴ = 0 := by
      rw [← Matrix.trace_conjTranspose_mul_self_eq_zero_iff]
      have he : (P * Qᴴ)ᴴ * (P * Qᴴ) = Q * (Pᴴ * P) * Qᴴ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
        simp [Matrix.mul_assoc]
      rw [he, ← hP]
      calc (Q * A * Qᴴ).trace = (Qᴴ * (Q * A)).trace := Matrix.trace_mul_comm _ _
        _ = (Qᴴ * Q * A).trace := by rw [Matrix.mul_assoc]
        _ = (A * (Qᴴ * Q)).trace := (Matrix.trace_mul_comm _ _).symm
        _ = (A * B).trace := by rw [hQ]
        _ = 0 := h0
    rw [hP, hQ]
    calc Pᴴ * P * (Qᴴ * Q) = Pᴴ * (P * Qᴴ) * Q := by
          simp [Matrix.mul_assoc]
      _ = 0 := by rw [hX]; simp
  · intro h0
    rw [hfrob, h0, Matrix.trace_zero]
