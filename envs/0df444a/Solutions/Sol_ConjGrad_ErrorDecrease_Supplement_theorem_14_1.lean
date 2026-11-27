-- Prove2me | solution 1 for ConjGrad.ErrorDecrease.Supplement.theorem_14_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:35:19.563204+00:00
-- url     : https://prove2.me/submissions/7afca5b5-a784-47ea-ac71-ce52dd760d3b

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_IsSpectralModel

open Matrix MeasureTheory

open ConjGrad
open ConjGrad.ErrorDecrease
open ConjGrad.ErrorDecrease.Supplement

/-- Theorem 14:1 (Hestenes–Stiefel 1952, p. 429): for a mass distribution related to `A` and `r₀` as
in §14, the correspondence `R ↦ R(A)r₀` is an isometry from the polynomials of degree at most
`n − 1` with the inner product `∫₀ˡ R R' dm` to `ℝⁿ` with the Euclidean inner product. -/
theorem solution {n : ℕ} (μ : Measure ℝ) (l : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (r₀ : Fin n → ℝ) (hrel : IsSpectralModel μ l A r₀) (R R' : Polynomial ℝ)
    (hR : R.degree < n) (hR' : R'.degree < n) :
    ∫ t, R.eval t * R'.eval t ∂μ = polyVec A r₀ R ⬝ᵥ polyVec A r₀ R' := by
      obtain ⟨lam, w, α, e, hG, _hw, horth, heig, hr, hα⟩ := hrel.data
      have key : ∀ (p : Polynomial ℝ) j, Polynomial.aeval A p *ᵥ e j = p.eval (lam j) • e j := by
        intro p j
        have hpow : ∀ k : ℕ, (A ^ k) *ᵥ e j = lam j ^ k • e j := by
          intro k
          induction k with
          | zero => simp
          | succ k ih =>
            rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, heig j, smul_smul, pow_succ', mul_comm]
        induction p using Polynomial.induction_on' with
        | add p q hp hq => simp [add_mulVec, hp, hq, add_smul]
        | monomial k a =>
          rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
            smul_mulVec, hpow, Polynomial.eval_monomial, smul_smul]
      have hvec : ∀ p : Polynomial ℝ, polyVec A r₀ p = ∑ j, (α j * p.eval (lam j)) • e j := by
        intro p
        simp only [polyVec, hr, mulVec_sum, mulVec_smul, key, smul_smul]
      have hdot : polyVec A r₀ R ⬝ᵥ polyVec A r₀ R' = ∑ j, w j * (R.eval (lam j) * R'.eval (lam j)) := by
        rw [hvec, hvec]
        simp only [sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul, horth, smul_eq_mul]
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← hα j]; ring
      rw [hdot]
      have hdeg : (R * R').natDegree ≤ 2 * n - 1 := by
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0
          have : R = 0 := Polynomial.degree_eq_bot.mp (by
            simpa using (show R.degree < ((0:ℕ) : WithBot ℕ) from hR))
          simp [this]
        · have h1 : R.natDegree ≤ n - 1 := by
            have := Polynomial.natDegree_lt_iff_degree_lt (p := R) (n := n)
            by_cases hR0 : R = 0
            · simp [hR0]
            · have := (Polynomial.natDegree_lt_iff_degree_lt hR0).mpr hR; omega
          have h2 : R'.natDegree ≤ n - 1 := by
            by_cases hR0 : R' = 0
            · simp [hR0]
            · have := (Polynomial.natDegree_lt_iff_degree_lt hR0).mpr hR'; omega
          have := Polynomial.natDegree_mul_le (p := R) (q := R')
          omega
      have := (hG.2 (R * R') hdeg).2
      simpa [Polynomial.eval_mul] using this
