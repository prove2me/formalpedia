-- Prove2me | solution 1 for DirectFidelity.State.eq_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:55:04.172585+00:00
-- url     : https://prove2.me/submissions/52d7a40d-36ae-484f-9039-ddcc39ae2f87

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_DirectFidelity_State_Setting
open scoped MatrixOrder ComplexOrder
set_option autoImplicit false

open DirectFidelity.State

theorem solution (n : ℕ) (ρ σ : Matrix (Q n) (Q n) ℂ) (hρ : IsPure ρ)
    (hσ : WildeQIT.IsDensityOperator σ) :
    ((CFC.sqrt (CFC.sqrt ρ * σ * CFC.sqrt ρ)).trace.re) ^ 2 = ((ρ * σ).trace).re := by
  rcases hρ with ⟨ψ, hψ, rfl⟩
  set P : Matrix (Q n) (Q n) ℂ := Matrix.vecMulVec ψ (star ψ)
  have hHerm : P.IsHermitian := by
    ext i j
    simp [P, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, mul_comm]
  have hdot : ∑ x : Q n, star (ψ x) * ψ x = 1 := by
    simpa [dotProduct, Pi.star_apply] using hψ
  have h_idem : P * P = P := by
    ext i j
    simp only [P, Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.star_apply]
    have hsum : ∑ x : Q n, ψ i * star (ψ x) * (ψ x * star (ψ j)) =
        (ψ i * star (ψ j)) * ∑ x : Q n, star (ψ x) * ψ x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => by ring
    rw [hsum, hdot, mul_one]
  have h_tr_P : P.trace = 1 := by
    simp only [P, Matrix.trace, Matrix.diag_apply, Matrix.vecMulVec_apply, Pi.star_apply]
    have hsum : ∑ x : Q n, ψ x * star (ψ x) = ∑ x : Q n, star (ψ x) * ψ x :=
      Finset.sum_congr rfl fun x _ => mul_comm _ _
    rw [hsum, hdot]
  have hP_psd : P.PosSemidef := by
    have h1 : (P.conjTranspose * P).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self P
    rwa [hHerm.eq, h_idem] at h1
  have hP_nonneg : 0 ≤ P := Matrix.nonneg_iff_posSemidef.mpr hP_psd
  have h_sqrt_P : CFC.sqrt P = P :=
    (CFC.sqrt_eq_iff P P hP_nonneg hP_nonneg).mpr h_idem
  set c : ℂ := (P * σ).trace
  have h_sandwich : P * σ * P = c • P := by
    ext i j
    simp only [P, c, Matrix.mul_apply, Matrix.trace, Matrix.diag_apply,
      Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.star_apply, smul_eq_mul]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => by ring
  have h_sand_psd : (P * σ * P).PosSemidef := by
    have h1 := hσ.1.conjTranspose_mul_mul_same P
    rwa [hHerm.eq] at h1
  have hc_nonneg : 0 ≤ c := by
    have htr : (P * σ * P).trace = c := by
      rw [h_sandwich, Matrix.trace_smul, h_tr_P, smul_eq_mul, mul_one]
    rw [← htr]
    exact h_sand_psd.trace_nonneg
  have hc_re_nonneg : 0 ≤ c.re := (Complex.nonneg_iff.mp hc_nonneg).1
  have hc_eq_re : ((c.re : ℝ) : ℂ) = c := by
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp hc_nonneg).2
  set r : ℝ := Real.sqrt c.re
  have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg c.re
  set B : Matrix (Q n) (Q n) ℂ := r • P
  have hB_psd : B.PosSemidef := hP_psd.smul hr_nonneg
  have hB_nonneg : 0 ≤ B := Matrix.nonneg_iff_posSemidef.mpr hB_psd
  have h_sand_nonneg : 0 ≤ P * σ * P := Matrix.nonneg_iff_posSemidef.mpr h_sand_psd
  have hB_sq : B * B = P * σ * P := by
    simp only [B, Matrix.smul_mul, Matrix.mul_smul, h_idem, smul_smul]
    have hr2 : r * r = c.re := by
      rw [← sq, Real.sq_sqrt hc_re_nonneg]
    rw [hr2, h_sandwich, ← hc_eq_re]
    rfl
  have h_sqrt_sand : CFC.sqrt (P * σ * P) = B :=
    (CFC.sqrt_eq_iff (P * σ * P) B h_sand_nonneg hB_nonneg).mpr hB_sq
  rw [h_sqrt_P, h_sqrt_sand]
  have hB_tr : (B.trace).re = r := by
    simp only [B, Matrix.trace_smul, h_tr_P, Complex.real_smul, mul_one, Complex.ofReal_re]
  rw [hB_tr, Real.sq_sqrt hc_re_nonneg]
