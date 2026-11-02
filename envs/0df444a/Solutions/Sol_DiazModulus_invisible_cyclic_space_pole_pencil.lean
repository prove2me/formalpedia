-- Prove2me | solution 1 for DiazModulus.invisible_cyclic_space_pole_pencil
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-01T09:30:17.163194+00:00
-- url     : https://prove2.me/submissions/6f1a5589-67f2-40e5-815c-2a867bf958f0

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_binary_quadratic_dvd_of_coprime_mul_eq
import Theorems.Thm_DiazModulus_quadratic_space_mem_iff_numerator

open Complex ComplexConjugate

/-! # The poles of an invisible cyclic space: `S(WB) = {O_P}`

Let `f ∈ WB ∖ H₀` with `f · u M(u) = R(u)`, `deg M ≤ 2`, `M ≠ 0`, `deg R ≤ 4`. By
`quadratic_space_mem_iff_numerator`, `f · u P² = N(u)` with `N = P² A + a₁ P Q S₁ + a₂ Q (Q S₁ + P S₂)`,
so `N M = R P²` by transcendence. All divisibility steps are `binary_quadratic_dvd_of_coprime_mul_eq`.
* `a₂ = 0`: otherwise `Q² S₁ · a₂ M = P (R P − P A M − a₁ Q S₁ M − a₂ Q S₂ M)` (`d = 6`, `e = 2`; the
  degree budget uses `deg S₂ ≤ 2`) gives `M = k P` with `k ≠ 0`; cancelling `P`,
  `Q² S₁ · a₂ k = P (R − k (P A + a₁ Q S₁ + a₂ Q S₂))` and the lemma with `e = 0` gives `a₂ k = 0`.
* Then `(P A + a₁ Q S₁) M = R P`. If `a₁ = 0`, `f = A(u)/u ∈ H₀`; otherwise
  `Q S₁ · a₁ M = P (R − A M)` (`d = 4`, `e = 2`) gives `M ∈ Q̄ P`, and `f = A(u)/u + a₁ g₁`. -/

namespace R21b_SB

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

/-- The degree budget leaves no room: `L = 0`. -/
theorem kl_zero {P L : (↥Qbar)[X]} {e : ℕ} (he : e ≤ 1)
    (h : ∃ L₀ : (↥Qbar)[X], L = P * L₀ ∧ (L₀ = 0 ∨ L₀.natDegree + 2 ≤ e)) : L = 0 := by
  obtain ⟨L₀, hL, rfl | h0⟩ := h
  · simpa using hL
  · omega

end R21b_SB

open DiazModulus R21b_SB in
open Polynomial in
theorem solution (u : ℂ) (hu : u ∉ Qbar) (P Q S₁ S₂ : (↥Qbar)[X])
    (hcop : IsCoprime P Q) (hdeg : max P.natDegree Q.natDegree = 2) (hS₁ : S₁.natDegree ≤ 2) (hS₂ : S₂.natDegree ≤ 2)
    (hPS : IsCoprime P S₁) (hP2 : P.coeff 2 ≠ 0 ∨ S₁.coeff 2 ≠ 0)
    (M R : (↥Qbar)[X]) (hM : M.natDegree ≤ 2) (hM0 : M ≠ 0) (hR : R.natDegree ≤ 4)
    (f : ℂ) (hf : f ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2)} : Set ℂ))
    (hf0 : f ∉ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ)) (hfM : f * (u * aeval u M) = aeval u R) :
    (∃ k : ↥Qbar, M = C k * P) ∧
      f ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P)} : Set ℂ) := by
  have hu0 := u_ne_zero hu
  have hQ0 := q_ne_zero hcop hdeg
  have hP0 := q_ne_zero hcop.symm (by rw [max_comm]; exact hdeg)
  have hS0 := s_ne_zero hPS hP2
  have hP : P.natDegree ≤ 2 := hdeg ▸ le_max_left _ _
  have hQ : Q.natDegree ≤ 2 := hdeg ▸ le_max_right _ _
  have hPu : aeval u P ≠ 0 := fun h => hP0 (aeval_eq_zero hu h)
  obtain ⟨A, a₁, a₂, hA, he⟩ := ((quadratic_space_mem_iff_numerator u hu P Q S₁ S₂ hP0 hQ0).2 f).1 hf
  -- `N M = R P²`
  have hNM : (P ^ 2 * A + C a₁ * (P * Q * S₁) + C a₂ * (Q * (Q * S₁ + P * S₂))) * M = R * P ^ 2 := by
    rw [← sub_eq_zero]
    apply aeval_eq_zero hu
    simp only [map_sub, map_add, map_mul, map_pow, aeval_C, am] at he ⊢
    linear_combination (-(aeval u M)) * he + (aeval u P ^ 2) * hfM
  -- `f = A(u)/u + a₁ g₁ + a₂ g₂`
  have hfe : f = (A.coeff 1 : ℂ) + A.coeff 2 * u + A.coeff 0 * u⁻¹ +
      a₁ * (aeval u Q * aeval u S₁ / (u * aeval u P)) +
      a₂ * (aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2)) := by
    apply mul_right_cancel₀ (mul_ne_zero hu0 (pow_ne_zero 2 hPu))
    rw [he]
    simp only [map_add, map_mul, map_pow, aeval_C, am, quad_eval u hA]
    field_simp
    ring
  have hF6 : P.natDegree = 2 ∨ (Q ^ 2 * S₁).natDegree = 6 :=
    (deg_cond hdeg hS₁ hP2).imp_right fun ⟨h1, h2, _⟩ => by
      rw [natDegree_mul (pow_ne_zero 2 hQ0) hS0, natDegree_pow]; omega
  -- `a₂ = 0`
  have ha₂ : a₂ = 0 := by
    by_contra ha₂
    obtain ⟨k, hk⟩ := of_kl ha₂ (binary_quadratic_dvd_of_coprime_mul_eq P (Q ^ 2 * S₁) (C a₂ * M)
      (R * P - P * A * M - C a₁ * (Q * S₁ * M) - C a₂ * (Q * S₂ * M)) 6 2
      (hcop.pow_right.mul_right hPS) (mul_ne_zero (pow_ne_zero 2 hQ0) hS0) hF6
      ((natDegree_C_mul_le _ _).trans hM) (by
        have d1 := natDegree_mul_le_of_le hR hP
        have d2 := natDegree_mul_le_of_le (natDegree_mul_le_of_le hP hA) hM
        have d3 := (natDegree_C_mul_le a₁ _).trans
          (natDegree_mul_le_of_le (natDegree_mul_le_of_le hQ hS₁) hM)
        have d4 := (natDegree_C_mul_le a₂ _).trans
          (natDegree_mul_le_of_le (natDegree_mul_le_of_le hQ hS₂) hM)
        have s1 := natDegree_sub_le (R * P) (P * A * M)
        have s2 := natDegree_sub_le (R * P - P * A * M) (C a₁ * (Q * S₁ * M))
        have s3 := natDegree_sub_le (R * P - P * A * M - C a₁ * (Q * S₁ * M)) (C a₂ * (Q * S₂ * M))
        omega)
      (by linear_combination hNM))
    have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hM0 hk
    have h2 : (P ^ 2 * A + C a₁ * (P * Q * S₁) + C a₂ * (Q * (Q * S₁ + P * S₂))) * C k = R * P :=
      mul_left_cancel₀ hP0 (by rw [hk] at hNM; linear_combination hNM)
    have h0 := kl_zero zero_le_one (binary_quadratic_dvd_of_coprime_mul_eq P (Q ^ 2 * S₁) (C (a₂ * k))
      (R - C k * (P * A + C a₁ * (Q * S₁) + C a₂ * (Q * S₂))) 6 0
      (hcop.pow_right.mul_right hPS) (mul_ne_zero (pow_ne_zero 2 hQ0) hS0) hF6 (natDegree_C _).le (by
        have d1 := natDegree_mul_le_of_le hP hA
        have d2 := (natDegree_C_mul_le a₁ _).trans (natDegree_mul_le_of_le hQ hS₁)
        have d3 := (natDegree_C_mul_le a₂ _).trans (natDegree_mul_le_of_le hQ hS₂)
        have s1 := natDegree_add_le (P * A) (C a₁ * (Q * S₁))
        have s2 := natDegree_add_le (P * A + C a₁ * (Q * S₁)) (C a₂ * (Q * S₂))
        have s3 := natDegree_C_mul_le k (P * A + C a₁ * (Q * S₁) + C a₂ * (Q * S₂))
        have s4 := natDegree_sub_le R (C k * (P * A + C a₁ * (Q * S₁) + C a₂ * (Q * S₂)))
        omega)
      (by rw [C_mul]; linear_combination h2))
    exact mul_ne_zero ha₂ hk0 (C_eq_zero.1 h0)
  rw [ha₂, C_0, zero_mul, add_zero] at hNM
  have h3 : (P * A + C a₁ * (Q * S₁)) * M = R * P :=
    mul_left_cancel₀ hP0 (by linear_combination hNM)
  by_cases ha₁ : a₁ = 0
  · refine absurd ?_ hf0
    convert mem3 (u := u) (A.coeff 1) (A.coeff 2) (A.coeff 0) using 1
    rw [hfe, ha₁, ha₂]; push_cast; ring
  refine ⟨of_kl ha₁ (binary_quadratic_dvd_of_coprime_mul_eq P (Q * S₁) (C a₁ * M) (R - A * M) 4 2
    (hcop.mul_right hPS) (mul_ne_zero hQ0 hS0)
    ((deg_cond hdeg hS₁ hP2).imp_right fun ⟨h1, h2, _⟩ => by rw [natDegree_mul hQ0 hS0]; omega)
    ((natDegree_C_mul_le _ _).trans hM) (by
      have d1 := natDegree_mul_le_of_le hA hM
      have s1 := natDegree_sub_le R (A * M)
      omega)
    (by linear_combination h3)), ?_⟩
  convert mem4 (u := u) (A.coeff 1) (A.coeff 2) (A.coeff 0) a₁ using 1
  rw [hfe, ha₂]; push_cast; ring
