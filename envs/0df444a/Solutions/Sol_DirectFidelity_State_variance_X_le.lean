-- Prove2me | solution 1 for DirectFidelity.State.variance_X_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:09:22.937781+00:00
-- url     : https://prove2.me/submissions/29e8b3ef-94dd-49e7-b8e4-87241769c01c

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_DirectFidelity_State_Setting

namespace Aux_DirectFidelity_State_variance_X_le
open DirectFidelity.State

theorem pauli_orth1 (a b c d : Fin 2) :
    ∑ j : Fin 4, pauli1 j a b * star (pauli1 j c d) = if a = c ∧ b = d then 2 else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [pauli1, Fin.sum_univ_four] <;> norm_num

theorem pauli_orth {n : ℕ} (y x y' x' : Q n) :
    ∑ k : P n, W k y x * star (W k y' x') = if y = y' ∧ x = x' then (2 : ℂ) ^ n else 0 := by
  have e1 : ∀ k : P n, W k y x * star (W k y' x') =
      ∏ i, (pauli1 (k i) (y i) (x i) * star (pauli1 (k i) (y' i) (x' i))) := by
    intro k
    unfold W
    rw [star_prod, ← Finset.prod_mul_distrib]
  simp only [e1]
  rw [← Fintype.prod_sum (fun i j => pauli1 j (y i) (x i) * star (pauli1 j (y' i) (x' i)))]
  simp only [pauli_orth1]
  by_cases h : y = y' ∧ x = x'
  · rw [if_pos h]
    obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h]
    have : ∃ i, ¬ (y i = y' i ∧ x i = x' i) := by
      by_contra hc
      push_neg at hc
      exact h ⟨funext fun i => (hc i).1, funext fun i => (hc i).2⟩
    obtain ⟨i, hi⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem trace_mul_W {n : ℕ} (σ : Matrix (Q n) (Q n) ℂ) (k : P n) :
    (σ * W k).trace = ∑ z : Q n × Q n, σ z.1 z.2 * W k z.2 z.1 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Fintype.sum_prod_type]

theorem parseval {n : ℕ} (σ : Matrix (Q n) (Q n) ℂ) :
    ∑ k : P n, (σ * W k).trace * star ((σ * W k).trace) =
      (2 : ℂ) ^ n * ∑ z : Q n × Q n, σ z.1 z.2 * star (σ z.1 z.2) := by
  simp only [trace_mul_W, star_sum, Finset.sum_mul_sum, star_mul']
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_comm]
  have : ∀ z' : Q n × Q n, ∑ k : P n, σ z.1 z.2 * W k z.2 z.1 * (star (σ z'.1 z'.2) *
      star (W k z'.2 z'.1)) = σ z.1 z.2 * star (σ z'.1 z'.2) *
      (if z.2 = z'.2 ∧ z.1 = z'.1 then (2 : ℂ) ^ n else 0) := by
    intro z'
    rw [← pauli_orth, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp only [this]
  rw [Finset.sum_eq_single z]
  · simp; ring
  · intro z' _ hz'
    have : ¬ (z.2 = z'.2 ∧ z.1 = z'.1) := by
      rintro ⟨h1, h2⟩; exact hz' (Prod.ext h2 h1).symm
    rw [if_neg this, mul_zero]
  · intro h; exact absurd (Finset.mem_univ z) h

end Aux_DirectFidelity_State_variance_X_le

open DirectFidelity.State Aux_DirectFidelity_State_variance_X_le in
theorem solution (n : ℕ) (ρ σ : Matrix (Q n) (Q n) ℂ) (hρ : IsPure ρ)
    (hσ : WildeQIT.IsDensityOperator σ) :
    ∑ k : P n, prob ρ k * X ρ σ k ^ 2 - ((ρ * σ).trace).re ^ 2 ≤
        ((σ * σ).trace).re - ((ρ * σ).trace).re ^ 2 ∧
      ((σ * σ).trace).re - ((ρ * σ).trace).re ^ 2 ≤ 1 := by
  have hH : σ.IsHermitian := hσ.1.1
  have hherm : ∀ x y, σ y x = star (σ x y) := by
    intro x y
    have := congrFun (congrFun hH y) x
    rw [Matrix.conjTranspose_apply] at this
    exact this.symm
  have hd : (0 : ℝ) < dim n := by unfold dim; positivity
  -- Re tr(σσ) = Σ |σ_xy|²
  have hss : ((σ * σ).trace).re = ∑ z : Q n × Q n, (σ z.1 z.2 * star (σ z.1 z.2)).re := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rw [Fintype.sum_prod_type, Complex.re_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hherm x y]
  constructor
  · have hterm : ∀ k : P n, prob ρ k * X ρ σ k ^ 2 ≤ chi σ k ^ 2 := by
      intro k
      unfold prob X
      by_cases h : chi ρ k = 0
      · rw [h]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
        exact sq_nonneg _
      · rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero 2 h)]
    have hchi : ∀ k : P n, chi σ k ^ 2 ≤ ((σ * W k).trace * star ((σ * W k).trace)).re / dim n := by
      intro k
      unfold chi
      rw [div_pow, Real.sq_sqrt hd.le]
      apply div_le_div_of_nonneg_right _ hd.le
      rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_apply]
      nlinarith [sq_nonneg ((σ * W k).trace).im]
    have hpars := congrArg Complex.re (parseval σ)
    rw [Complex.re_sum] at hpars
    have h2n : ((2 : ℂ) ^ n * ∑ z : Q n × Q n, σ z.1 z.2 * star (σ z.1 z.2)).re =
        dim n * ∑ z : Q n × Q n, (σ z.1 z.2 * star (σ z.1 z.2)).re := by
      rw [show (2 : ℂ) ^ n = ((2 ^ n : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul,
        Complex.re_sum]
      rfl
    rw [h2n] at hpars
    have hsum : ∑ k : P n, prob ρ k * X ρ σ k ^ 2 ≤ ((σ * σ).trace).re := by
      calc ∑ k : P n, prob ρ k * X ρ σ k ^ 2
          ≤ ∑ k : P n, ((σ * W k).trace * star ((σ * W k).trace)).re / dim n :=
            Finset.sum_le_sum fun k _ => (hterm k).trans (hchi k)
        _ = (∑ k : P n, ((σ * W k).trace * star ((σ * W k).trace)).re) / dim n := by
            rw [Finset.sum_div]
        _ = ((σ * σ).trace).re := by rw [hpars, hss]; field_simp
    linarith
  · -- tr(σ²) ≤ 1 via eigenvalues
    have hspec := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hspec
    set U := (hH.eigenvectorUnitary : Matrix (Q n) (Q n) ℂ) with hU
    set D := Matrix.diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hH.eigenvalues) with hD
    have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
    have hσσ : (σ * σ).trace = (D * D).trace := by
      rw [hspec]
      have : U * D * star U * (U * D * star U) = U * (D * D) * star U := by
        rw [show U * D * star U * (U * D * star U) = U * D * (star U * U) * D * star U by
          simp only [Matrix.mul_assoc]]
        rw [hUU, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
      rw [this, Matrix.trace_mul_cycle, hUU, Matrix.one_mul]
    have hDD : (D * D).trace = ∑ i, ((hH.eigenvalues i : ℂ)) ^ 2 := by
      rw [hD, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
      simp [sq]
    have hl0 : ∀ i, 0 ≤ hH.eigenvalues i := hσ.1.eigenvalues_nonneg
    have hl1 : ∑ i, hH.eigenvalues i = 1 := by
      have := hH.trace_eq_sum_eigenvalues
      rw [hσ.2] at this
      have := congrArg Complex.re this
      simp only [Complex.one_re, Complex.re_sum, RCLike.ofReal_re] at this
      exact this.symm
    have hle : ((σ * σ).trace).re ≤ 1 := by
      rw [hσσ, hDD, Complex.re_sum]
      have : ∀ i, (((hH.eigenvalues i : ℂ)) ^ 2).re = hH.eigenvalues i ^ 2 := by
        intro i
        rw [show ((hH.eigenvalues i : ℂ)) ^ 2 = (((hH.eigenvalues i) ^ 2 : ℝ) : ℂ) by push_cast; rfl,
          Complex.ofReal_re]
      simp only [this]
      calc ∑ i, hH.eigenvalues i ^ 2 ≤ ∑ i, hH.eigenvalues i := by
            refine Finset.sum_le_sum fun i _ => ?_
            have h1 : hH.eigenvalues i ≤ 1 := by
              rw [← hl1]
              exact Finset.single_le_sum (f := hH.eigenvalues) (fun j _ => hl0 j)
                (Finset.mem_univ i)
            nlinarith [hl0 i]
        _ = 1 := hl1
    nlinarith [sq_nonneg ((ρ * σ).trace).re]
