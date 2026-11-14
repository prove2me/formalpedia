-- Prove2me | solution 1 for BosonicLearn.loewner_trace_bound
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T06:56:49.133239+00:00
-- url     : https://prove2.me/submissions/f2bef3cd-9f0a-48ac-925c-c36dda55aba3

import Mathlib

open scoped Matrix MatrixOrder

noncomputable section

/-- The trace of a product of two positive semidefinite matrices is non-negative. -/
private lemma trace_mul_nonneg {ι : Type} [Fintype ι] [DecidableEq ι] {P Q : Matrix ι ι ℝ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) : 0 ≤ (P * Q).trace := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hQ.nonneg
  have h := (hP.mul_mul_conjTranspose_same B).trace_nonneg
  have e : (P * (star B * B)).trace = (B * P * Bᴴ).trace := by
    rw [Matrix.star_eq_conjTranspose, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  rw [e]
  exact h

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (S D : Matrix ι ι ℝ) (hS : S.PosDef)
    (hD : D.PosSemidef) (c : ℝ) (hc : 0 ≤ c) (hDS : (c • S - D).PosSemidef) :
    (S⁻¹ * D * S⁻¹ * D).trace ≤ c ^ 2 * Fintype.card ι := by
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS.isUnit
  have hinv : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hdet
  have hSi : S⁻¹.PosSemidef := hS.inv.posSemidef
  have hSiH : S⁻¹ᴴ = S⁻¹ := hS.isHermitian.inv
  have hP : (S⁻¹ * D * S⁻¹).PosSemidef := by
    have h := hD.conjTranspose_mul_mul_same S⁻¹
    rwa [hSiH] at h
  -- first step: Tr(P D) ≤ c Tr(S⁻¹ D)
  have h1 := trace_mul_nonneg hP hDS
  have e1 : (S⁻¹ * D * S⁻¹ * (c • S - D)).trace =
      c * (S⁻¹ * D).trace - (S⁻¹ * D * S⁻¹ * D).trace := by
    rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
      Matrix.mul_assoc (S⁻¹ * D), hinv, Matrix.mul_one]
  rw [e1] at h1
  -- second step: Tr(S⁻¹ D) ≤ c d
  have h2 := trace_mul_nonneg hSi hDS
  have e2 : (S⁻¹ * (c • S - D)).trace = c * Fintype.card ι - (S⁻¹ * D).trace := by
    rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, hinv,
      Matrix.trace_one]
  rw [e2] at h2
  nlinarith [mul_nonneg hc h2]
