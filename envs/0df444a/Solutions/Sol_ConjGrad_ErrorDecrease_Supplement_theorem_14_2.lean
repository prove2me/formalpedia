-- Prove2me | solution 1 for ConjGrad.ErrorDecrease.Supplement.theorem_14_2
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T12:48:20.135473+00:00
-- url     : https://prove2.me/submissions/038eda30-936f-4995-9abe-0392b3ece3d5

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_IsSpectralModel

open Matrix MeasureTheory Polynomial

open ConjGrad.ErrorDecrease.Supplement

theorem solution {n : ℕ} (μ : Measure ℝ) (l : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (r₀ : Fin n → ℝ) (hrel : IsSpectralModel μ l A r₀) (R R' : Polynomial ℝ)
    (hR : R.degree < n) (hR' : R'.degree < n) :
    ∫ t, R.eval t * R'.eval t * t ∂μ = (A *ᵥ polyVec A r₀ R) ⬝ᵥ polyVec A r₀ R' := by
  rcases hrel.data with ⟨lam, w, α, e, hGauss, hw, horth, heig, hr0, hα2⟩
  -- A^k acts as lam j^k on eigenvector e j
  have hpow (j : Fin n) (k : ℕ) : A ^ k *ᵥ e j = lam j ^ k • e j := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, heig j, Matrix.mulVec_smul, ih]
      simp [smul_smul, pow_succ, mul_comm]
  -- aeval A P acts as P.eval (lam j) on e j
  have heval (j : Fin n) (P : Polynomial ℝ) :
      Polynomial.aeval A P *ᵥ e j = P.eval (lam j) • e j := by
    induction P using Polynomial.induction_on' with
    | add p q hp hq =>
      simp only [Polynomial.aeval_add, add_mulVec, hp, hq, Polynomial.eval_add, add_smul]
    | monomial k a =>
      simp only [Polynomial.aeval_monomial, Polynomial.eval_monomial,
        Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.smul_mulVec,
        hpow j k, smul_smul]
  -- polyVec expansion in the eigenbasis
  have hpv (P : Polynomial ℝ) : polyVec A r₀ P = ∑ j, (α j * P.eval (lam j)) • e j := by
    simp only [polyVec, hr0, mulVec_sum, mulVec_smul, heval, smul_smul]
  -- dotProduct in the orthonormal eigenbasis
  have hdot (c d : Fin n → ℝ) :
      (∑ j, c j • e j) ⬝ᵥ (∑ j, d j • e j) = ∑ j, c j * d j := by
    classical
    simp only [sum_dotProduct, smul_dotProduct, dotProduct_sum,
      dotProduct_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    have hinner : ∑ x, c x * (e x ⬝ᵥ e j) = c j := by
      rw [Finset.sum_eq_single j]
      · rw [horth j j, if_pos rfl]; ring
      · intro k _ hkj
        rw [horth k j, if_neg hkj]; ring
      · intro hj; exfalso; exact hj (Finset.mem_univ j)
    rw [hinner]
    ring
  -- RHS as the weighted node sum
  have hRHS : (A *ᵥ polyVec A r₀ R) ⬝ᵥ polyVec A r₀ R' =
      ∑ j, w j * R.eval (lam j) * R'.eval (lam j) * lam j := by
    simp only [hpv]
    have hA : A *ᵥ ∑ j, (α j * R.eval (lam j)) • e j =
        ∑ j, (α j * R.eval (lam j) * lam j) • e j := by
      simp only [mulVec_sum, mulVec_smul, heig, smul_smul]
    rw [hA]
    rw [hdot]
    apply Finset.sum_congr rfl
    intro j _
    rw [← hα2 j]
    ring
  -- LHS via the Gauss rule applied to R * R' * X
  have hdeg : (R * R' * Polynomial.X).natDegree ≤ 2 * n - 1 := by
    by_cases hR0 : R = 0
    · simp [hR0]
    · by_cases hR'0 : R' = 0
      · simp [hR'0]
      · have hnR : R.natDegree < n := by
          rw [Polynomial.degree_eq_natDegree hR0] at hR
          exact_mod_cast hR
        have hnR' : R'.natDegree < n := by
          rw [Polynomial.degree_eq_natDegree hR'0] at hR'
          exact_mod_cast hR'
        calc (R * R' * Polynomial.X).natDegree
            ≤ (R * R').natDegree + Polynomial.X.natDegree := Polynomial.natDegree_mul_le
          _ ≤ R.natDegree + R'.natDegree + 1 := by
            rw [Polynomial.natDegree_X]
            have := Polynomial.natDegree_mul_le (p := R) (q := R')
            omega
          _ ≤ 2 * n - 1 := by omega
  have hG := (hGauss.2 (R * R' * Polynomial.X) hdeg)
  have hLHS : ∫ t, R.eval t * R'.eval t * t ∂μ =
      ∑ j, w j * R.eval (lam j) * R'.eval (lam j) * lam j := by
    have heq : (fun t => R.eval t * R'.eval t * t) =
        (fun t => (R * R' * Polynomial.X).eval t) := by
      funext t; simp [Polynomial.eval_mul, Polynomial.eval_X]
    rw [heq, hG.2]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Polynomial.eval_mul, Polynomial.eval_X]
    ring
  rw [hLHS, hRHS]
