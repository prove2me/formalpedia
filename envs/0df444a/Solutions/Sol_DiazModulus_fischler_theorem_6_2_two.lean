-- Prove2me | solution 1 for DiazModulus.fischler_theorem_6_2_two
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-18T16:18:56.33319+00:00
-- url     : https://prove2.me/submissions/130ad1bc-4b81-45f4-96a9-097f1bac5d91

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_fischler_linear_pow_prod_mem
import Theorems.Thm_DiazModulus_fischler_power_span_finrank
import Theorems.Thm_DiazModulus_fischler_rational_hull

open Complex ComplexConjugate

/-! # Fischler 2001, Theorem 6.2 (2)

Let `P = Λ²` with `Λ = Σᵢ λᵢXᵢ` and every coefficient of `P` in `ℒ̃`. Then every product `λᵢλⱼ` lies in `ℒ̃`,
so the `Q̄`-span of `λ₁, …, λ_m` has dimension at most `2`. Write `λ = Σₐ cₐwₐ` with complex `cₐ` and algebraic
vectors `wₐ`, the number of terms being that dimension. It suffices to write `λ = aφ₁ + bφ₂` with `φ₁, φ₂`
algebraic, since then `Λ = aΣᵢφ₁ᵢXᵢ + bΣᵢφ₂ᵢXᵢ`. With `0`, `1` or `2` terms, take respectively
`a = b = 0`; `a = c₀`, `φ₁ = w₀`, `b = 0`; and `a = c₀`, `b = c₁`, `φ₁ = w₀`, `φ₂ = w₁`. -/

open DiazModulus MvPolynomial in
theorem solution {m : ℕ} (P : MvPolynomial (Fin m) ℂ)
    (hP : ∀ s, P.coeff s ∈ LogAlgTilde) (Λ : Fin m → ℂ)
    (hPΛ : P = (∑ i, MvPolynomial.C (Λ i) * MvPolynomial.X i) ^ 2) :
    ∃ φ₁ φ₂ : Fin m → ℂ, (∀ i, φ₁ i ∈ Qbar) ∧ (∀ i, φ₂ i ∈ Qbar) ∧ ∃ a b : ℂ,
      P = (MvPolynomial.C a * (∑ i, MvPolynomial.C (φ₁ i) * MvPolynomial.X i) +
        MvPolynomial.C b * (∑ i, MvPolynomial.C (φ₂ i) * MvPolynomial.X i)) ^ 2 := by
  subst hPΛ
  have hn := (DiazModulus.fischler_power_span_finrank le_rfl Λ
    (DiazModulus.fischler_linear_pow_prod_mem Λ hP)).1
  obtain ⟨n, c, w, hn', -, -, hwQ, hvw, -⟩ := DiazModulus.fischler_rational_hull Λ
  rw [← hn'] at hn
  suffices h : ∃ φ₁ φ₂ : Fin m → ℂ, (∀ i, φ₁ i ∈ Qbar) ∧ (∀ i, φ₂ i ∈ Qbar) ∧ ∃ a b : ℂ,
      ∀ i, Λ i = a * φ₁ i + b * φ₂ i by
    obtain ⟨φ₁, φ₂, h₁, h₂, a, b, hab⟩ := h
    refine ⟨φ₁, φ₂, h₁, h₂, a, b, ?_⟩
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hab, C_add, C_mul, C_mul]
    ring
  have hΛ : ∀ i, Λ i = ∑ a, c a * w a i := fun i => by simpa using congr_fun hvw i
  interval_cases n
  · exact ⟨0, 0, fun _ => zero_mem _, fun _ => zero_mem _, 0, 0, fun i => by simp [hΛ i]⟩
  · exact ⟨w 0, 0, hwQ 0, fun _ => zero_mem _, c 0, 0, fun i => by simp [hΛ i]⟩
  · exact ⟨w 0, w 1, hwQ 0, hwQ 1, c 0, c 1, fun i => by simp [hΛ i, Fin.sum_univ_two]⟩
