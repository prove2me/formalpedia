-- Prove2me | solution 1 for DiazModulus.invisible_two_orbit_space_pole_pencil
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-01T09:30:22.591289+00:00
-- url     : https://prove2.me/submissions/c3d465bf-48aa-4344-acdd-18f0f9c856c3

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_binary_quadratic_dvd_of_coprime_mul_eq
import Theorems.Thm_DiazModulus_quadratic_space_mem_iff_numerator

open Complex ComplexConjugate

/-! # The poles of an invisible two-orbit space: `S(WA) = {O_P, O_Q}`

Let `f ∈ WA ∖ H₀` with `f · u M(u) = R(u)`, `deg M ≤ 2`, `M ≠ 0`, `deg R ≤ 4`. By
`quadratic_space_mem_iff_numerator`, `f · u P Q = N(u)` with `N = P Q A + a₁ Q² S₁ + a₂ P² S₂`, so
`N M = R P Q` by transcendence. If `a₁ ≠ 0`, then `Q² S₁ · a₁ M = P (R Q − Q A M − a₂ P S₂ M)`, and
`binary_quadratic_dvd_of_coprime_mul_eq` at `P` (`d = 6`, `e = 2`) gives `a₁ M = P L₀` with `L₀`
constant, so `M ∈ Q̄ P`. Symmetrically `a₂ ≠ 0` gives `M ∈ Q̄ Q`. Both cannot hold (`P`, `Q` coprime of
degree `2`), and `a₁ = a₂ = 0` would put `f = A(u)/u` in `H₀`. So exactly one `aᵢ` is non-zero, and
`f = A(u)/u + aᵢ gᵢ` lies in `H₀ + Q̄ gᵢ`. -/

namespace R21b_SA

open DiazModulus Polynomial

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem smul_def' (c : ↥Qbar) (z : ℂ) : c • z = (c : ℂ) * z := rfl

theorem u_ne_zero {u : ℂ} (hu : u ∉ Qbar) : u ≠ 0 := fun h => hu (h ▸ Qbar.zero_mem)

theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {p : (↥Qbar)[X]} (h : aeval u p = 0) : p = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) p h

theorem q_ne_zero {p q : (↥Qbar)[X]} (hcop : IsCoprime p q)
    (hdeg : max p.natDegree q.natDegree = 2) : q ≠ 0 := by
  rintro rfl
  have := natDegree_eq_zero_of_isUnit (isCoprime_zero_right.1 hcop)
  simp at hdeg
  omega

/-- `deg P < 2` forces `deg Q = 2` and `deg S = 2`. -/
theorem deg_cond {P Q S : (↥Qbar)[X]} (hdeg : max P.natDegree Q.natDegree = 2) (hS : S.natDegree ≤ 2)
    (hP2 : P.coeff 2 ≠ 0 ∨ S.coeff 2 ≠ 0) :
    P.natDegree = 2 ∨ (Q.natDegree = 2 ∧ S.natDegree = 2 ∧ S ≠ 0) := by
  by_cases h : P.natDegree = 2
  · exact Or.inl h
  have hP : P.natDegree < 2 := lt_of_le_of_ne (hdeg ▸ le_max_left _ _) h
  have hS2 := hP2.resolve_left fun h' => h' (coeff_eq_zero_of_natDegree_lt hP)
  exact Or.inr ⟨by omega, le_antisymm hS (le_natDegree_of_ne_zero hS2), fun h0 => by simp [h0] at hS2⟩

theorem s_ne_zero {P S : (↥Qbar)[X]} (hPS : IsCoprime P S) (hP2 : P.coeff 2 ≠ 0 ∨ S.coeff 2 ≠ 0) :
    S ≠ 0 := by
  rintro rfl
  have := natDegree_eq_zero_of_isUnit (isCoprime_zero_right.1 hPS)
  simp [coeff_eq_zero_of_natDegree_lt (show P.natDegree < 2 by omega)] at hP2

/-- `a M = P L₀` with `L₀` constant and `a ≠ 0`: `M ∈ Q̄ P`. -/
theorem of_kl {P M : (↥Qbar)[X]} {a : ↥Qbar} (ha : a ≠ 0)
    (h : ∃ L₀ : (↥Qbar)[X], C a * M = P * L₀ ∧ (L₀ = 0 ∨ L₀.natDegree + 2 ≤ 2)) :
    ∃ k : ↥Qbar, M = C k * P := by
  obtain ⟨L₀, hL, hL₀⟩ := h
  have hd : L₀.natDegree = 0 := by rcases hL₀ with rfl | h0 <;> [simp; omega]
  refine ⟨a⁻¹ * L₀.coeff 0, ?_⟩
  rw [eq_C_of_natDegree_eq_zero hd] at hL
  calc M = C a⁻¹ * (C a * M) := by rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ ha, C_1, one_mul]
    _ = C (a⁻¹ * L₀.coeff 0) * P := by rw [hL, C_mul]; ring

/-- One pole: `a₁ ≠ 0` forces `M ∈ Q̄ P`. -/
theorem pole {P Q S₁ S₂ A M R : (↥Qbar)[X]} {a₁ a₂ : ↥Qbar} (hcop : IsCoprime P Q)
    (hdeg : max P.natDegree Q.natDegree = 2) (hS₁ : S₁.natDegree ≤ 2) (hS₂ : S₂.natDegree ≤ 2)
    (hPS : IsCoprime P S₁) (hP2 : P.coeff 2 ≠ 0 ∨ S₁.coeff 2 ≠ 0) (hM : M.natDegree ≤ 2)
    (hR : R.natDegree ≤ 4) (hA : A.natDegree ≤ 2) (ha : a₁ ≠ 0)
    (h : (P * Q * A + C a₁ * (Q ^ 2 * S₁) + C a₂ * (P ^ 2 * S₂)) * M = R * P * Q) :
    ∃ k : ↥Qbar, M = C k * P := by
  have hQ0 := q_ne_zero hcop hdeg
  have hS0 := s_ne_zero hPS hP2
  have hP : P.natDegree ≤ 2 := hdeg ▸ le_max_left _ _
  have hQ : Q.natDegree ≤ 2 := hdeg ▸ le_max_right _ _
  refine of_kl ha (binary_quadratic_dvd_of_coprime_mul_eq P (Q ^ 2 * S₁) (C a₁ * M)
    (R * Q - Q * A * M - C a₂ * (P * S₂ * M)) 6 2 (hcop.pow_right.mul_right hPS)
    (mul_ne_zero (pow_ne_zero 2 hQ0) hS0)
    ((deg_cond hdeg hS₁ hP2).imp_right fun ⟨h1, h2, _⟩ => by
      rw [natDegree_mul (pow_ne_zero 2 hQ0) hS0, natDegree_pow]; omega)
    ((natDegree_C_mul_le _ _).trans hM) ?_ (by linear_combination h))
  have d1 := natDegree_mul_le_of_le hR hQ
  have d2 := natDegree_mul_le_of_le (natDegree_mul_le_of_le hQ hA) hM
  have d3 := (natDegree_C_mul_le a₂ _).trans (natDegree_mul_le_of_le (natDegree_mul_le_of_le hP hS₂) hM)
  have s1 := natDegree_sub_le (R * Q) (Q * A * M)
  have s2 := natDegree_sub_le (R * Q - Q * A * M) (C a₂ * (P * S₂ * M))
  omega

/-- `M` cannot be proportional to both `P` and `Q`. -/
theorem not_both {P Q M : (↥Qbar)[X]} (hcop : IsCoprime P Q) (hdeg : max P.natDegree Q.natDegree = 2)
    (hM0 : M ≠ 0) {k k' : ↥Qbar} (hk : M = C k * P) (hk' : M = C k' * Q) : False := by
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hM0 hk
  have e : P = C (k⁻¹ * k') * Q := by
    rw [C_mul, mul_assoc, ← hk', hk, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hk0, C_1, one_mul]
  rw [e] at hcop hdeg
  have h0 := natDegree_eq_zero_of_isUnit (isCoprime_self.1 (IsCoprime.mul_left_iff.1 hcop).2)
  have h1 := natDegree_C_mul_le (k⁻¹ * k') Q
  omega

theorem quad_eval (u : ℂ) {A : (↥Qbar)[X]} (hA : A.natDegree ≤ 2) :
    aeval u A = (A.coeff 0 : ℂ) + (A.coeff 1 : ℂ) * u + (A.coeff 2 : ℂ) * u ^ 2 := by
  rw [aeval_eq_sum_range' (n := 3) (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, smul_def']
  ring

theorem mem4 {u g : ℂ} (c₀ c₁ c₂ a : ↥Qbar) :
    (c₀ : ℂ) + c₁ * u + c₂ * u⁻¹ + a * g ∈ Submodule.span Qbar ({1, u, u⁻¹, g} : Set ℂ) := by
  have h : ∀ x ∈ ({1, u, u⁻¹, g} : Set ℂ), x ∈ Submodule.span Qbar ({1, u, u⁻¹, g} : Set ℂ) :=
    fun x hx => Submodule.subset_span hx
  have := add_mem (add_mem (add_mem (Submodule.smul_mem _ c₀ (h 1 (by simp)))
    (Submodule.smul_mem _ c₁ (h u (by simp)))) (Submodule.smul_mem _ c₂ (h u⁻¹ (by simp))))
    (Submodule.smul_mem _ a (h g (by simp)))
  simpa only [smul_def', mul_one] using this

theorem mem3 {u : ℂ} (c₀ c₁ c₂ : ↥Qbar) :
    (c₀ : ℂ) + c₁ * u + c₂ * u⁻¹ ∈ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) := by
  have h : ∀ x ∈ ({1, u, u⁻¹} : Set ℂ), x ∈ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) :=
    fun x hx => Submodule.subset_span hx
  have := add_mem (add_mem (Submodule.smul_mem _ c₀ (h 1 (by simp)))
    (Submodule.smul_mem _ c₁ (h u (by simp)))) (Submodule.smul_mem _ c₂ (h u⁻¹ (by simp)))
  simpa only [smul_def', mul_one] using this

end R21b_SA

open DiazModulus R21b_SA in
open Polynomial in
theorem solution (u : ℂ) (hu : u ∉ Qbar) (P Q S₁ S₂ : (↥Qbar)[X])
    (hcop : IsCoprime P Q) (hdeg : max P.natDegree Q.natDegree = 2) (hS₁ : S₁.natDegree ≤ 2) (hS₂ : S₂.natDegree ≤ 2)
    (hPS : IsCoprime P S₁) (hQS : IsCoprime Q S₂)
    (hP2 : P.coeff 2 ≠ 0 ∨ S₁.coeff 2 ≠ 0) (hQ2 : Q.coeff 2 ≠ 0 ∨ S₂.coeff 2 ≠ 0)
    (M R : (↥Qbar)[X]) (hM : M.natDegree ≤ 2) (hM0 : M ≠ 0) (hR : R.natDegree ≤ 4)
    (f : ℂ) (hf : f ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u P * aeval u S₂ / (u * aeval u Q)} : Set ℂ))
    (hf0 : f ∉ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ)) (hfM : f * (u * aeval u M) = aeval u R) :
    ((∃ k : ↥Qbar, M = C k * P) ∧
        f ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P)} : Set ℂ)) ∨
    ((∃ k : ↥Qbar, M = C k * Q) ∧
        f ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u P * aeval u S₂ / (u * aeval u Q)} : Set ℂ)) := by
  have hu0 := u_ne_zero hu
  have hQ0 := q_ne_zero hcop hdeg
  have hdeg' : max Q.natDegree P.natDegree = 2 := by rw [max_comm]; exact hdeg
  have hP0 := q_ne_zero hcop.symm hdeg'
  have hPu : aeval u P ≠ 0 := fun h => hP0 (aeval_eq_zero hu h)
  have hQu : aeval u Q ≠ 0 := fun h => hQ0 (aeval_eq_zero hu h)
  obtain ⟨A, a₁, a₂, hA, he⟩ := ((quadratic_space_mem_iff_numerator u hu P Q S₁ S₂ hP0 hQ0).1 f).1 hf
  -- `N M = R P Q`
  have hNM : (P * Q * A + C a₁ * (Q ^ 2 * S₁) + C a₂ * (P ^ 2 * S₂)) * M = R * P * Q := by
    rw [← sub_eq_zero]
    apply aeval_eq_zero hu
    simp only [map_sub, map_add, map_mul, map_pow, aeval_C, am] at he ⊢
    linear_combination (-(aeval u M)) * he + (aeval u P * aeval u Q) * hfM
  -- `f = A(u)/u + a₁ g₁ + a₂ g₂`
  have hfe : f = (A.coeff 1 : ℂ) + A.coeff 2 * u + A.coeff 0 * u⁻¹ +
      a₁ * (aeval u Q * aeval u S₁ / (u * aeval u P)) + a₂ * (aeval u P * aeval u S₂ / (u * aeval u Q)) := by
    apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hu0 hPu) hQu)
    rw [he]
    simp only [map_add, map_mul, map_pow, aeval_C, am, quad_eval u hA]
    field_simp
    ring
  have poleQ : a₂ ≠ 0 → ∃ k : ↥Qbar, M = C k * Q := fun ha₂ =>
    pole (a₁ := a₂) (a₂ := a₁) hcop.symm hdeg' hS₂ hS₁ hQS hQ2 hM hR hA ha₂ (by linear_combination hNM)
  by_cases ha₁ : a₁ = 0
  · by_cases ha₂ : a₂ = 0
    · refine absurd ?_ hf0
      convert mem3 (u := u) (A.coeff 1) (A.coeff 2) (A.coeff 0) using 1
      rw [hfe, ha₁, ha₂]; push_cast; ring
    · refine Or.inr ⟨poleQ ha₂, ?_⟩
      convert mem4 (u := u) (A.coeff 1) (A.coeff 2) (A.coeff 0) a₂ using 1
      rw [hfe, ha₁]; push_cast; ring
  · obtain ⟨k, hk⟩ := pole hcop hdeg hS₁ hS₂ hPS hP2 hM hR hA ha₁ hNM
    have ha₂ : a₂ = 0 := by
      by_contra ha₂
      obtain ⟨k', hk'⟩ := poleQ ha₂
      exact not_both hcop hdeg hM0 hk hk'
    refine Or.inl ⟨⟨k, hk⟩, ?_⟩
    convert mem4 (u := u) (A.coeff 1) (A.coeff 2) (A.coeff 0) a₁ using 1
    rw [hfe, ha₂]; push_cast; ring
