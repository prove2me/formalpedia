-- Prove2me | solution 1 for DissipativePrep.Unique.unitary_covariance
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T04:26:41.656993+00:00
-- url     : https://prove2.me/submissions/d041d942-85a9-4e44-8b8f-6b5d1d3a51ad

import Mathlib
import Definitions.Def_DissipativePrep_Unique_Model

open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P16

namespace DissipativePrep.Unique

lemma gksl_apply {d : ℕ} (D : LindbladData d) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    gkslGenerator D ρ = ∑ k, D.jump k * ρ * (D.jump k)ᴴ - driftK D * ρ - ρ * (driftK D)ᴴ := by
  simp [gkslGenerator, cpGenerator, sandwich, mul_assoc]

lemma conj_gen {d m : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (h1 : Uᴴ * U = 1) (h2 : U * Uᴴ = 1)
    (V : Fin m → Matrix (Fin d) (Fin d) ℂ) (σ : Matrix (Fin d) (Fin d) ℂ) :
    ∑ k, (U * V k * Uᴴ) * σ * (U * V k * Uᴴ)ᴴ
      - ((1 / 2 : ℂ) • ∑ k, (U * V k * Uᴴ)ᴴ * (U * V k * Uᴴ)) * σ
      - σ * ((1 / 2 : ℂ) • ∑ k, (U * V k * Uᴴ)ᴴ * (U * V k * Uᴴ))ᴴ
    = U * (∑ k, V k * (Uᴴ * σ * U) * (V k)ᴴ
      - ((1 / 2 : ℂ) • ∑ k, (V k)ᴴ * V k) * (Uᴴ * σ * U)
      - (Uᴴ * σ * U) * ((1 / 2 : ℂ) • ∑ k, (V k)ᴴ * V k)ᴴ) * Uᴴ := by
  have hK : ∀ k, (U * V k * Uᴴ)ᴴ * (U * V k * Uᴴ) = U * ((V k)ᴴ * V k) * Uᴴ := by
    intro k
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc U * ((V k)ᴴ * Uᴴ) * (U * V k * Uᴴ) = U * (V k)ᴴ * (Uᴴ * U) * V k * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp [Matrix.mul_assoc]
  set A : Matrix (Fin d) (Fin d) ℂ := (1 / 2 : ℂ) • ∑ k, (V k)ᴴ * V k with hA
  have hKU : (1 / 2 : ℂ) • ∑ k, (U * V k * Uᴴ)ᴴ * (U * V k * Uᴴ) = U * A * Uᴴ := by
    simp only [hK, hA, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
  have e1 : ∀ X, U * X * Uᴴ * σ = U * (X * (Uᴴ * σ * U)) * Uᴴ := fun X => by
    calc U * X * Uᴴ * σ = U * X * Uᴴ * σ * (U * Uᴴ) := by rw [h2, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have e2 : ∀ X, σ * (U * X * Uᴴ) = U * ((Uᴴ * σ * U) * X) * Uᴴ := fun X => by
    calc σ * (U * X * Uᴴ) = (U * Uᴴ) * σ * (U * X * Uᴴ) := by rw [h2, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]
  have e3 : ∑ k, (U * V k * Uᴴ) * σ * (U * V k * Uᴴ)ᴴ
      = U * (∑ k, V k * (Uᴴ * σ * U) * (V k)ᴴ) * Uᴴ := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hAhh : (U * A * Uᴴ)ᴴ = U * Aᴴ * Uᴴ := by
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hKU, e3, e1, hAhh, e2]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

lemma gksl_prep_eq {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (g : Fin n → ℝ)
    (σ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    gkslGenerator (prepData U g 0 Matrix.isHermitian_zero) σ =
      U * gkslGenerator (prepData 1 g 0 Matrix.isHermitian_zero) (Uᴴ * σ * U) * Uᴴ := by
  have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have h2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  rw [gksl_apply, gksl_apply]
  have key := conj_gen U h1 h2 (fun k : Fin n => ((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k) σ
  have e0 : ∀ k : Fin n, ((Real.sqrt (2 * g k) : ℝ) : ℂ) • (U * lower k * Uᴴ) =
      U * (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k) * Uᴴ := fun k => by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have e1 : ∀ k : Fin n, ((Real.sqrt (2 * g k) : ℝ) : ℂ) • (1 * lower k * (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)ᴴ) =
      ((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k := fun k => by
    rw [Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul]
  have g1 : ∀ k : Fin n, (prepData U g 0 Matrix.isHermitian_zero).jump k =
      U * (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k) * Uᴴ := fun k => by
    show ((Real.sqrt (2 * g k) : ℝ) : ℂ) • (U * lower k * Uᴴ) = _
    exact e0 k
  have g2 : ∀ k : Fin n, (prepData 1 g 0 Matrix.isHermitian_zero).jump k =
      ((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k := fun k => by
    show ((Real.sqrt (2 * g k) : ℝ) : ℂ) • (1 * lower k * (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)ᴴ) = _
    exact e1 k
  have hdr : (prepData U g 0 Matrix.isHermitian_zero).drift = 0 := rfl
  have hdr1 : (prepData 1 g 0 Matrix.isHermitian_zero).drift = 0 := rfl
  have g3 : driftK (prepData U g 0 Matrix.isHermitian_zero) = (1 / 2 : ℂ) • ∑ k : Fin n,
      (U * (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k) * Uᴴ)ᴴ *
        (U * (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k) * Uᴴ) := by
    rw [driftK, hdr, smul_zero, zero_add]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [g1 k]
  have g4 : driftK (prepData 1 g 0 Matrix.isHermitian_zero) = (1 / 2 : ℂ) • ∑ k : Fin n,
      (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k)ᴴ * (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k) := by
    rw [driftK, hdr1, smul_zero, zero_add]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [g2 k]
  have s1 : ∀ τ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ,
      ∑ k, (prepData U g 0 Matrix.isHermitian_zero).jump k * τ * ((prepData U g 0 Matrix.isHermitian_zero).jump k)ᴴ
      = ∑ k : Fin n, (U * (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k) * Uᴴ) * τ *
          (U * (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k) * Uᴴ)ᴴ := fun τ =>
    Finset.sum_congr rfl fun k _ => by rw [g1 k]
  have s2 : ∀ τ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ,
      ∑ k, (prepData 1 g 0 Matrix.isHermitian_zero).jump k * τ * ((prepData 1 g 0 Matrix.isHermitian_zero).jump k)ᴴ
      = ∑ k : Fin n, (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k) * τ *
          (((Real.sqrt (2 * g k) : ℝ) : ℂ) • lower k)ᴴ := fun τ =>
    Finset.sum_congr rfl fun k _ => by rw [g2 k]
  rw [s1, s2, g3, g4]
  exact key

end DissipativePrep.Unique

open DissipativePrep.Unique

theorem solution {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (g : Fin n → ℝ) (hg : ∀ k, 0 < g k) :
    (∀ σ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ,
      gkslGenerator (prepData U g 0 Matrix.isHermitian_zero) σ =
        U * gkslGenerator (prepData 1 g 0 Matrix.isHermitian_zero) (Uᴴ * σ * U) * Uᴴ) ∧
    ∀ (σ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (μ : ℂ),
      gkslGenerator (prepData U g 0 Matrix.isHermitian_zero) σ = μ • σ ↔
        gkslGenerator (prepData 1 g 0 Matrix.isHermitian_zero) (Uᴴ * σ * U) = μ • (Uᴴ * σ * U) := by
  have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have h2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  refine ⟨fun σ => gksl_prep_eq U hU g σ, fun σ μ => ?_⟩
  rw [gksl_prep_eq U hU g σ]
  constructor
  · intro h
    have := congrArg (fun X => Uᴴ * X * U) h
    simp only [Matrix.mul_assoc] at this
    rw [← Matrix.mul_assoc Uᴴ U, h1, Matrix.one_mul] at this
    simpa [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, h1] using this
  · intro h
    rw [h]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    congr 1
    calc U * (Uᴴ * (σ * (U * Uᴴ))) = (U * Uᴴ) * σ * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
      _ = σ := by rw [h2]; simp

