-- Prove2me | solution 1 for DirectFidelity.State.eq_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:12:38.513424+00:00
-- url     : https://prove2.me/submissions/12a09a91-4dfa-4d24-a703-8df7fd909148

import Mathlib
import Definitions.Def_DirectFidelity_State_Setting

namespace Aux_DirectFidelity_State_eq_2
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

theorem polar {n : ℕ} (ρ σ : Matrix (Q n) (Q n) ℂ) :
    ∑ k : P n, (ρ * W k).trace * star ((σ * W k).trace) =
      (2 : ℂ) ^ n * ∑ z : Q n × Q n, ρ z.1 z.2 * star (σ z.1 z.2) := by
  simp only [trace_mul_W, star_sum, Finset.sum_mul_sum, star_mul']
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_comm]
  have : ∀ z' : Q n × Q n, ∑ k : P n, ρ z.1 z.2 * W k z.2 z.1 * (star (σ z'.1 z'.2) *
      star (W k z'.2 z'.1)) = ρ z.1 z.2 * star (σ z'.1 z'.2) *
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

theorem pauli_herm1 (j : Fin 4) (a b : Fin 2) : star (pauli1 j a b) = pauli1 j b a := by
  fin_cases j <;> fin_cases a <;> fin_cases b <;> simp [pauli1]

theorem W_herm {n : ℕ} (k : P n) : Matrix.conjTranspose (W k) = W k := by
  ext x y
  rw [Matrix.conjTranspose_apply]
  unfold W
  rw [star_prod]
  exact Finset.prod_congr rfl fun i _ => pauli_herm1 _ _ _

theorem trace_im {n : ℕ} (τ : Matrix (Q n) (Q n) ℂ) (hτ : τ.IsHermitian) (k : P n) :
    ((τ * W k).trace).im = 0 := by
  have h : star ((τ * W k).trace) = (τ * W k).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, W_herm, hτ.eq,
      Matrix.trace_mul_comm]
  rw [Complex.star_def] at h
  exact Complex.conj_eq_iff_im.mp h

theorem trace_mul_herm {n : ℕ} (ρ σ : Matrix (Q n) (Q n) ℂ) (hσ : σ.IsHermitian) :
    (ρ * σ).trace = ∑ z : Q n × Q n, ρ z.1 z.2 * star (σ z.1 z.2) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have := congrFun (congrFun hσ.eq y) x
  rw [Matrix.conjTranspose_apply] at this
  rw [← this]

theorem eq2 (n : ℕ) (ρ σ : Matrix (Q n) (Q n) ℂ) (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    ((ρ * σ).trace).re = ∑ k : P n, chi ρ k * chi σ k := by
  have hd : (0 : ℝ) < dim n := by unfold dim; positivity
  have hpol := congrArg Complex.re (polar ρ σ)
  rw [← trace_mul_herm ρ σ hσ] at hpol
  rw [show (2 : ℂ) ^ n = ((2 ^ n : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul,
    Complex.re_sum] at hpol
  have hterm : ∀ k : P n, ((ρ * W k).trace * star ((σ * W k).trace)).re =
      ((ρ * W k).trace).re * ((σ * W k).trace).re := by
    intro k
    rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, trace_im σ hσ k]
    ring
  simp only [hterm] at hpol
  have hchi : ∀ k : P n, chi ρ k * chi σ k =
      ((ρ * W k).trace).re * ((σ * W k).trace).re / dim n := by
    intro k
    unfold chi
    rw [div_mul_div_comm, Real.mul_self_sqrt hd.le]
  simp only [hchi]
  rw [← Finset.sum_div, hpol]
  unfold dim
  field_simp

end Aux_DirectFidelity_State_eq_2

open DirectFidelity.State Aux_DirectFidelity_State_eq_2 in
theorem solution (n : ℕ) (ρ σ : Matrix (Q n) (Q n) ℂ) (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    ((ρ * σ).trace).re = ∑ k : P n, chi ρ k * chi σ k :=
  eq2 n ρ σ hρ hσ
