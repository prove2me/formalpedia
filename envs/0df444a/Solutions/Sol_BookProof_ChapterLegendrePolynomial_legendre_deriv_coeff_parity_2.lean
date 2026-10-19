-- Prove2me | solution 2 for BookProof.ChapterLegendrePolynomial.legendre_deriv_coeff_parity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:42:46.532025+00:00
-- url     : https://prove2.me/submissions/277caf9d-5cc9-4a60-86aa-9200941b6f64

import Mathlib
import Definitions.Def_ChapterLegendrePolynomial
import Theorems.Thm_BookProof_ChapterLegendrePolynomial_legendreAux_ode
import Theorems.Thm_BookProof_ChapterLegendrePolynomial_legendre_natDegree_le
import Theorems.Thm_BookProof_ChapterLegendrePolynomial_legendre_deriv_coeff_eq_zero
-- Generated from ChapterLegendrePolynomial.lean — theorem BookProof.ChapterLegendrePolynomial.legendre_deriv_coeff_parity
open BookProof.ChapterLegendrePolynomial



open Polynomial
theorem h43_aux_rec (l j : ℕ) :
    ((j : ℝ) + 2) * ((j : ℝ) + 1) * (legendreAux l).coeff (j + 2)
      = ((j : ℝ) * ((j : ℝ) + 1) - (l : ℝ) * ((l : ℝ) + 1)) * (legendreAux l).coeff j := by
  have h := congrArg (fun p => p.coeff j) (BookProof.ChapterLegendrePolynomial.legendreAux_ode l)
  simp only [sub_mul, one_mul, mul_assoc, coeff_sub, coeff_add, coeff_C_mul, coeff_zero] at h
  rcases j with _ | _ | j
  · simp [coeff_iterate_derivative, coeff_X_pow_mul', coeff_derivative, Nat.descFactorial] at h ⊢
    linarith
  · simp [coeff_iterate_derivative, coeff_X_pow_mul', coeff_derivative, coeff_X_mul, Nat.descFactorial] at h ⊢
    linarith
  · simp [coeff_iterate_derivative, coeff_X_pow_mul', coeff_derivative, coeff_X_mul, Nat.descFactorial] at h ⊢
    push_cast at h ⊢
    ring_nf at h ⊢
    linarith

theorem h43_leg_rec (l j : ℕ) :
    ((j : ℝ) + 2) * ((j : ℝ) + 1) * (legendre l).coeff (j + 2)
      = ((j : ℝ) * ((j : ℝ) + 1) - (l : ℝ) * ((l : ℝ) + 1)) * (legendre l).coeff j := by
  simp only [legendre, coeff_C_mul]
  linear_combination ((2 ^ l * (Nat.factorial l : ℝ))⁻¹) * h43_aux_rec l j

theorem h43_Ppar (l : ℕ) : ∀ d k : ℕ, l ≤ k + d → k % 2 ≠ l % 2 → (legendre l).coeff k = 0 := by
  intro d
  induction d with
  | zero =>
    intro k hk hp
    have : l < k := by
      rcases Nat.lt_or_ge l k with h | h
      · exact h
      · exfalso; apply hp; congr 1; omega
    exact coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (BookProof.ChapterLegendrePolynomial.legendre_natDegree_le l) this)
  | succ d ih =>
    intro k hk hp
    rcases Nat.lt_or_ge l k with h | h
    · exact coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (BookProof.ChapterLegendrePolynomial.legendre_natDegree_le l) h)
    have hkl : k < l := by
      rcases Nat.lt_or_ge k l with h' | h'
      · exact h'
      · exfalso; apply hp; congr 1; omega
    have h2 : (legendre l).coeff (k + 2) = 0 := ih (k + 2) (by omega) (by omega)
    have hr := h43_leg_rec l k
    rw [h2, mul_zero] at hr
    have hne : ((k : ℝ) * ((k : ℝ) + 1) - (l : ℝ) * ((l : ℝ) + 1)) ≠ 0 := by
      have : (k : ℝ) + 1 ≤ l := by exact_mod_cast hkl
      have hk0 : (0 : ℝ) ≤ k := by positivity
      nlinarith
    exact (mul_eq_zero.mp hr.symm).resolve_left hne

theorem h43_Ypar (l μ : ℕ) (hμ : μ ≤ l) (j : ℕ) (hp : j % 2 ≠ (l - μ) % 2) :
    (derivative^[μ] (legendre l)).coeff j = 0 := by
  rw [coeff_iterate_derivative, h43_Ppar l l (j + μ) (by omega) (by omega), smul_zero]

theorem solution (l μ : ℕ) (h : μ ≤ l) (j : ℕ)
    (hpar : j % 2 ≠ (l - μ) % 2) : (derivative^[μ] (legendre l)).coeff j = 0 := by
  exact h43_Ypar l μ h j hpar

