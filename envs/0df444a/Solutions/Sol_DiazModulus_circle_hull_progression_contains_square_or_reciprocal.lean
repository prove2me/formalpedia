-- Prove2me | solution 1 for DiazModulus.circle_hull_progression_contains_square_or_reciprocal
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-05T08:18:35.902554+00:00
-- url     : https://prove2.me/submissions/86ae8d03-6c8c-4330-99a7-4090844884d8

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_cubic_product_eq_square_normal_form

open Complex ComplexConjugate

/-!
# A progression through `1, u, ū` contains `u²`, `ū²` or some `1/(u − a)`

Let `u ∉ Q̄` with `ρ = u ū` algebraic, `b ≠ 0`, `h ∉ Q̄`, and `V = b (Q̄ + Q̄h + Q̄h² + Q̄h³)` with
`1, u, ū ∈ V`. Every element of `V` is `b P(h)` with `deg P ≤ 3` (`mem_progression_iff`), so
`1, u, u⁻¹ = ū/ρ` are `b Pᵢ(h)`. As `h` is transcendental, `P₁P₂ = P₀²`, and `P₀, P₁` are free since
`u ∉ Q̄`. By `cubic_product_eq_square_normal_form`, `(P₀, P₁, P₂) = G (Q₀Q₁, Q₁², Q₀²)` with
`G = aQ₀ + cQ₁`, whence `u Q₀(h) = Q₁(h)`. If `c = 0` then `u² = b a Q₁(h)³ ∈ V`; if `a = 0` then
`ū² = b ρ² c Q₀(h)³ ∈ V`; otherwise `1/(u + a/c) = b c Q₀(h)² Q₁(h) ∈ V`.
-/

namespace R4B_progression_cases

open DiazModulus Polynomial

/-- Outside `Q̄`, no non-zero polynomial over `Q̄` vanishes. -/
theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) :
    P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

theorem ne_zero_of_not_mem {u : ℂ} (hu : u ∉ Qbar) : u ≠ 0 :=
  fun h => hu (h ▸ Subfield.zero_mem _)

/-- `ρ = u ū` as a non-zero element of `Q̄`. -/
theorem exists_rho {u : ℂ} (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u)) :
    ∃ ρ : ↥Qbar, ρ ≠ 0 ∧ algebraMap (↥Qbar) ℂ ρ = u * conj u := by
  have hu0 := ne_zero_of_not_mem hu
  refine ⟨⟨u * conj u, mem_Qbar_iff.2 hρ⟩, fun h => ?_, rfl⟩
  have := congrArg (algebraMap (↥Qbar) ℂ) h
  rw [map_zero] at this
  exact mul_ne_zero hu0 ((_root_.map_ne_zero _).2 hu0) this

/-- `b (Q̄ + Q̄h + Q̄h² + Q̄h³)` is the set of `b P(h)` with `deg P ≤ 3`. -/
theorem mem_progression_iff {b h t : ℂ} :
    t ∈ Submodule.span (↥Qbar) (Set.range fun k : Fin 4 => b * h ^ (k : ℕ)) ↔
      ∃ P : (↥Qbar)[X], P.natDegree ≤ 3 ∧ t = b * aeval h P := by
  constructor
  · intro ht
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (↥Qbar)).1 ht
    refine ⟨∑ k : Fin 4, C (c k) * X ^ (k : ℕ),
      natDegree_sum_le_of_forall_le _ _ fun k _ =>
        (natDegree_C_mul_X_pow_le _ _).trans (by have := k.isLt; omega), ?_⟩
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, aeval_C, map_pow, aeval_X, Algebra.smul_def]
    ring
  · rintro ⟨P, hP, rfl⟩
    rw [aeval_eq_sum_range' (n := 4) (by omega), Finset.mul_sum]
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, Finset.mem_range.1 hi⟩, rfl⟩)

end R4B_progression_cases

open DiazModulus R4B_progression_cases Polynomial in
theorem solution (u b h : ℂ) (V : Submodule (↥Qbar) ℂ)
    (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u)) (hb : b ≠ 0) (hh : h ∉ Qbar)
    (hV : V = Submodule.span (↥Qbar) (Set.range fun k : Fin 4 => b * h ^ (k : ℕ)))
    (h1 : (1 : ℂ) ∈ V) (hu' : u ∈ V) (hū : conj u ∈ V) :
    u ^ 2 ∈ V ∨ conj u ^ 2 ∈ V ∨ ∃ a ∈ Qbar, a ≠ 0 ∧ (u - a)⁻¹ ∈ V := by
  subst hV
  have hu0 := ne_zero_of_not_mem hu
  have hū0 : conj u ≠ 0 := (_root_.map_ne_zero _).2 hu0
  obtain ⟨ρ, -, hρ'⟩ := exists_rho hu hρ
  have hui : u⁻¹ ∈ Submodule.span (↥Qbar) (Set.range fun k : Fin 4 => b * h ^ (k : ℕ)) := by
    have : u⁻¹ = ρ⁻¹ • conj u := by
      rw [Algebra.smul_def, map_inv₀, hρ', mul_inv_rev, mul_comm (conj u)⁻¹, mul_assoc,
        inv_mul_cancel₀ hū0, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ hū
  -- `1, u, u⁻¹` as values of polynomials of degree at most `3`
  obtain ⟨P₀, -, e₀⟩ := mem_progression_iff.1 h1
  obtain ⟨P₁, d₁, e₁⟩ := mem_progression_iff.1 hu'
  obtain ⟨P₂, d₂, e₂⟩ := mem_progression_iff.1 hui
  have hrel : P₁ * P₂ = P₀ ^ 2 := by
    refine sub_eq_zero.1 (aeval_eq_zero hh ?_)
    have : b ^ 2 * aeval h (P₁ * P₂ - P₀ ^ 2) = 0 := by
      rw [map_sub, map_mul, map_pow]
      linear_combination (-(b * aeval h P₂)) * e₁ - u * e₂ + mul_inv_cancel₀ hu0 +
        (b * aeval h P₀ + 1) * e₀
    exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero 2 hb)
  have hli : LinearIndependent (↥Qbar) ![P₀, P₁] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hev := congrArg (aeval h) hst
    rw [map_add, map_smul, map_smul, map_zero, Algebra.smul_def, Algebra.smul_def] at hev
    have hP := aeval_eq_zero hu (P := C s + C t * X) (by
      rw [map_add, map_mul, aeval_C, aeval_C, aeval_X]
      linear_combination b * hev + algebraMap (↥Qbar) ℂ s * e₀ + algebraMap (↥Qbar) ℂ t * e₁)
    have c0 := congrArg (coeff · 0) hP
    have c1 := congrArg (coeff · 1) hP
    exact ⟨by simpa using c0, by simpa using c1⟩
  -- the normal form, and `u Q₀(h) = Q₁(h)`
  obtain ⟨Q₀, Q₁, dQ₀, dQ₁, -, a, c, hP₀, hP₁, -⟩ :=
    cubic_product_eq_square_normal_form P₀ P₁ P₂ d₁ d₂ hli hrel
  rw [hP₀] at e₀
  rw [hP₁] at e₁
  simp only [map_mul, map_add, map_pow, aeval_C] at e₀ e₁
  have K : u * aeval h Q₀ = aeval h Q₁ := by
    linear_combination aeval h Q₀ * e₁ - aeval h Q₁ * e₀
  by_cases hc : c = 0
  · left
    subst hc
    simp only [map_zero, zero_mul, add_zero] at e₀
    have e : u ^ 2 = b * aeval h (C a * Q₁ ^ 3) := by
      simp only [map_mul, map_pow, aeval_C]
      linear_combination u ^ 2 * e₀ +
        b * algebraMap (↥Qbar) ℂ a * aeval h Q₁ * (u * aeval h Q₀ + aeval h Q₁) * K
    rw [e]
    exact mem_progression_iff.2
      ⟨_, (natDegree_C_mul_le _ _).trans (natDegree_pow_le.trans (by omega)), rfl⟩
  by_cases ha : a = 0
  · right; left
    subst ha
    simp only [map_zero, zero_mul, zero_add] at e₀
    have e : conj u ^ 2 = b * aeval h (C (ρ ^ 2 * c) * Q₀ ^ 3) := by
      simp only [map_mul, map_pow, aeval_C, hρ']
      linear_combination conj u ^ 2 * e₀ -
        conj u ^ 2 * b * algebraMap (↥Qbar) ℂ c * aeval h Q₀ * (u * aeval h Q₀ + aeval h Q₁) * K
    rw [e]
    exact mem_progression_iff.2
      ⟨_, (natDegree_C_mul_le _ _).trans (natDegree_pow_le.trans (by omega)), rfl⟩
  · right; right
    have hC : algebraMap (↥Qbar) ℂ c ≠ 0 := (_root_.map_ne_zero _).2 hc
    refine ⟨algebraMap (↥Qbar) ℂ (-(a / c)), (-(a / c)).2,
      (_root_.map_ne_zero _).2 (neg_ne_zero.2 (div_ne_zero ha hc)), ?_⟩
    have hαc : (u - algebraMap (↥Qbar) ℂ (-(a / c))) * algebraMap (↥Qbar) ℂ c =
        u * algebraMap (↥Qbar) ℂ c + algebraMap (↥Qbar) ℂ a := by
      rw [map_neg, map_div₀, sub_neg_eq_add, add_mul, div_mul_cancel₀ _ hC]
    have e : (u - algebraMap (↥Qbar) ℂ (-(a / c)))⁻¹ = b * aeval h (C c * Q₀ ^ 2 * Q₁) := by
      simp only [map_mul, map_pow, aeval_C]
      refine inv_eq_of_mul_eq_one_right ?_
      linear_combination b * aeval h Q₀ ^ 2 * aeval h Q₁ * hαc +
        b * aeval h Q₀ * aeval h Q₁ * algebraMap (↥Qbar) ℂ c * K - e₀
    rw [e]
    refine mem_progression_iff.2 ⟨_, ?_, rfl⟩
    have := natDegree_C_mul_le c (Q₀ ^ 2)
    have := natDegree_pow_le (p := Q₀) (n := 2)
    exact natDegree_mul_le.trans (by omega)

#print axioms solution
