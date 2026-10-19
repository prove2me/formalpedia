-- Prove2me | solution 2 for BookProof.ChapterSolidHarmonic.radialFactor_eval
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:52:51.285275+00:00
-- url     : https://prove2.me/submissions/2767f631-ad01-4e85-bb50-56872569bf53

import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterSolidHarmonicTools
import Mathlib
import Definitions.Def_ChapterSolidHarmonic
import Definitions.Def_ChapterLegendrePolynomial
import Theorems.Thm_BookProof_ChapterLegendrePolynomial_legendreAux_ode
import Theorems.Thm_BookProof_ChapterLegendrePolynomial_legendre_natDegree_le
import Theorems.Thm_BookProof_ChapterLegendrePolynomial_legendre_deriv_coeff_eq_zero
-- Generated from ChapterSolidHarmonic.lean — theorem BookProof.ChapterSolidHarmonic.radialFactor_eval
open BookProof.ChapterLegendrePolynomial
open BookProof.ChapterSolidHarmonic



open Laplacian InnerProductSpace Polynomial
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open BookProof.ChapterSolidHarmonicTools BookProof.ChapterLegendrePolynomial
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
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

theorem h43_desc (j μ : ℕ) :
    (j + 2) * (j + 1) * (j + 2 + μ).descFactorial μ = (j + μ + 2) * (j + μ + 1) * (j + μ).descFactorial μ := by
  have e1 := Nat.succ_descFactorial (j + μ + 1) μ
  have e2 := Nat.succ_descFactorial (j + μ) μ
  have a1 : j + μ + 1 + 1 - μ = j + 2 := by omega
  have a2 : j + μ + 1 - μ = j + 1 := by omega
  rw [a1] at e1; rw [a2] at e2
  have : j + 2 + μ = j + μ + 1 + 1 := by omega
  rw [this]
  calc (j + 2) * (j + 1) * (j + μ + 1 + 1).descFactorial μ
      = (j + 1) * ((j + 2) * (j + μ + 1 + 1).descFactorial μ) := by ring
    _ = (j + 1) * ((j + μ + 1 + 1) * (j + μ + 1).descFactorial μ) := by rw [e1]
    _ = (j + μ + 2) * ((j + 1) * (j + μ + 1).descFactorial μ) := by ring
    _ = (j + μ + 2) * ((j + μ + 1) * (j + μ).descFactorial μ) := by rw [e2]
    _ = _ := by ring


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

theorem h43_radialFactor_eval (e : E) {l μ : ℕ} (hμ : μ ≤ l) {x : E} (hx : x ≠ 0) :
    radialFactor e l μ x
      = ‖x‖ ^ (l - μ) * (derivative^[μ] (legendre l)).eval (⟪e, x⟫_ℝ / ‖x‖) := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hdeg : (derivative^[μ] (legendre l)).natDegree < l - μ + 1 := by
    rw [Nat.lt_succ_iff, natDegree_le_iff_coeff_eq_zero]
    intro k hk
    exact BookProof.ChapterLegendrePolynomial.legendre_deriv_coeff_eq_zero l μ k
      (by have : l - μ < k := by exact_mod_cast hk
          omega)
  rw [eval_eq_sum_range' hdeg, Finset.mul_sum]
  have himg : (Finset.range ((l - μ) / 2 + 1)).image (fun m => l - μ - 2 * m) ⊆ Finset.range (l - μ + 1) := by
    intro k hk
    simp only [Finset.mem_image, Finset.mem_range] at hk ⊢
    obtain ⟨m, _, rfl⟩ := hk
    omega
  rw [← Finset.sum_subset himg ?_]
  · rw [Finset.sum_image ?_]
    · unfold radialFactor
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm' : 2 * m ≤ l - μ := by
        have := Finset.mem_range.mp hm; omega
      have hp : ‖x‖ ^ (l - μ) = ‖x‖ ^ (l - μ - 2 * m) * (‖x‖ ^ 2) ^ m := by
        rw [← pow_mul, ← pow_add]; congr 1; omega
      rw [div_pow, hp]
      field_simp
    · intro a ha b hb hab
      simp only [Finset.coe_range, Set.mem_Iio] at ha hb
      simp only at hab
      omega
  · intro k hk hk'
    have : (derivative^[μ] (legendre l)).coeff k = 0 := by
      apply h43_Ypar l μ hμ k
      intro hpar
      apply hk'
      simp only [Finset.mem_image, Finset.mem_range] at hk ⊢
      refine ⟨(l - μ - k) / 2, by omega, by omega⟩
    rw [this, zero_mul, mul_zero]

theorem solution (e : E) {l μ : ℕ} (hμ : μ ≤ l) {x : E} (hx : x ≠ 0) :
    radialFactor e l μ x
      = ‖x‖ ^ (l - μ) * (derivative^[μ] (legendre l)).eval (⟪e, x⟫_ℝ / ‖x‖) := by
  exact h43_radialFactor_eval e hμ hx

