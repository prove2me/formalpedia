-- Prove2me | solution 1 for DiazModulus.cyclic_space_visible_to_four_dimensional_extensions_iff_common_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-01T09:25:30.249201+00:00
-- url     : https://prove2.me/submissions/6e448e83-b6d7-4dba-9a2c-34b5eb12a575

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_visible_to_four_dimensional_extensions_iff_visible_element_mem
import Theorems.Thm_DiazModulus_quadratic_fraction_extension_visible_element_mem_of_common_zero
import Theorems.Thm_DiazModulus_invisible_cyclic_space_u_multiplier_space_eq
import Theorems.Thm_DiazModulus_u_multiplier_space_le_span_no_degree_one_no_visible_element

open Complex ComplexConjugate

/-! # Visibility of a cyclic space: iff a common zero of `P` and `S₁`

`W = span(1, u, u⁻¹, g₁, g₂)` with `g₁ = Q(u) S₁(u)/(u P(u))`,
`g₂ = Q(u)(Q(u) S₁(u) + P(u) S₂(u))/(u P(u)²)` and `dim W = 5`. By
`visible_to_four_dimensional_extensions_iff_visible_element_mem`, visibility of `W` is
"W contains a `t_x`".
* `⇐`: `dim W = 5` gives `S₁ ∉ Q̄·P` (else `g₁ = k Q(u)/u ∈ H₀` and `dim W ≤ 4`). A common zero of
  `P, S₁` puts a `t_x` in `H₀ + Q̄g₁ ≤ W` by
  `quadratic_fraction_extension_visible_element_mem_of_common_zero`.
* `⇒`: with no common zero, `invisible_cyclic_space_u_multiplier_space_eq` gives
  `W ∩ u⁻¹W = span(1, u⁻¹)`, and `u_multiplier_space_le_span_no_degree_one_no_visible_element`
  excludes every `t_x`.
-/

namespace R21b_V4

open DiazModulus Polynomial

theorem tr_of_not_mem {u : ℂ} (hu : u ∉ Qbar) : Transcendental (↥Qbar) u := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact (Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1 fun h' => hu (mem_Qbar_iff.2 h')

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem smul_def' (c : ↥Qbar) (z : ℂ) : c • z = (c : ℂ) * z := rfl

theorem aeval_ne_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (hP : P ≠ 0) : aeval u P ≠ 0 :=
  fun h => hP (transcendental_iff.1 (tr_of_not_mem hu) P h)

theorem ne_zero_of_coprime {P Q : (↥Qbar)[X]} (hcop : IsCoprime P Q)
    (hdeg : max P.natDegree Q.natDegree = 2) : Q ≠ 0 := by
  rintro rfl
  have := natDegree_eq_zero_of_isUnit (isCoprime_zero_right.1 hcop)
  simp [this] at hdeg

/-- `R(u)/u ∈ H₀` when `deg R ≤ 2`. -/
theorem quad_div_mem {u : ℂ} (hu0 : u ≠ 0) {R : (↥Qbar)[X]} (hR : R.natDegree ≤ 2) :
    aeval u R / u ∈ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) := by
  have e : aeval u R / u = (R.coeff 1 : ℂ) + (R.coeff 2 : ℂ) * u + (R.coeff 0 : ℂ) * u⁻¹ := by
    rw [aeval_eq_sum_range' (n := 3) (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, smul_def']
    field_simp
    ring
  have hs : ∀ x ∈ ({1, u, u⁻¹} : Set ℂ), x ∈ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) :=
    fun x hx => Submodule.subset_span hx
  have := add_mem (add_mem (Submodule.smul_mem _ (R.coeff 1) (hs 1 (by simp)))
    (Submodule.smul_mem _ (R.coeff 2) (hs u (by simp))))
    (Submodule.smul_mem _ (R.coeff 0) (hs u⁻¹ (by simp)))
  rw [e]
  simpa only [smul_def', mul_one] using this

/-- If `g₁ ∈ H₀` then `dim span(1, u, u⁻¹, g₁, g₂) ≤ 4`. -/
theorem drop {u g₁ g₂ : ℂ} (hg : g₁ ∈ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ)) :
    Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, u⁻¹, g₁, g₂} : Set ℂ)) ≤ 4 := by
  have hle : Submodule.span Qbar ({1, u, u⁻¹, g₁, g₂} : Set ℂ) ≤
      Submodule.span Qbar ((({1, u, u⁻¹, g₂} : Finset ℂ)) : Set ℂ) := by
    simp only [Finset.coe_insert, Finset.coe_singleton]
    have h3 : Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) ≤ Submodule.span Qbar ({1, u, u⁻¹, g₂} : Set ℂ) :=
      Submodule.span_mono (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
    refine Submodule.span_le.2 ?_
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact ⟨Submodule.subset_span (by simp), Submodule.subset_span (by simp),
      Submodule.subset_span (by simp), h3 hg, Submodule.subset_span (by simp)⟩
  exact (Submodule.finrank_mono hle).trans ((finrank_span_finset_le_card _).trans Finset.card_le_four)

/-- `S = k P` makes `Q(u) S(u)/(u P(u)) = k Q(u)/u` lie in `H₀`. -/
theorem mem_H {u : ℂ} (hu : u ∉ Qbar) {P Q : (↥Qbar)[X]} (hP : P ≠ 0) (hQ : Q.natDegree ≤ 2)
    (k : ↥Qbar) :
    aeval u Q * aeval u (C k * P) / (u * aeval u P) ∈ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Qbar.zero_mem)
  have hPu := aeval_ne_zero hu hP
  have e : aeval u Q * aeval u (C k * P) / (u * aeval u P) = aeval u (C k * Q) / u := by
    simp only [map_mul, aeval_C, am]; field_simp
  rw [e]
  exact quad_div_mem hu0 ((natDegree_C_mul_le _ _).trans hQ)

end R21b_V4

open DiazModulus R21b_V4 in
open Polynomial in
theorem solution (u : ℂ) (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u))
    (P Q S₁ S₂ : (↥Qbar)[X]) (hcop : IsCoprime P Q) (hdeg : max P.natDegree Q.natDegree = 2) (hS₁ : S₁.natDegree ≤ 2) (hS₂ : S₂.natDegree ≤ 2)
    (h5 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2)} : Set ℂ)) = 5) :
    (∃ w ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2)} : Set ℂ), w ∉ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) ∧
        ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
          ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, u⁻¹, w} : Set ℂ)) ↔
    (¬ IsCoprime P S₁ ∨ (P.coeff 2 = 0 ∧ S₁.coeff 2 = 0)) := by
  have hP0 : P ≠ 0 := ne_zero_of_coprime hcop.symm (by rwa [max_comm])
  have hQ2 : Q.natDegree ≤ 2 := hdeg ▸ le_max_right _ _
  have sub : ∀ x ∈ ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
      aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2)} : Set ℂ), x ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2)} : Set ℂ) :=
    fun x hx => Submodule.subset_span hx
  have hle : Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P)} : Set ℂ) ≤
      Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2)} : Set ℂ) :=
    Submodule.span_mono (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto)
  refine (visible_to_four_dimensional_extensions_iff_visible_element_mem u hu hρ _
    (sub 1 (by simp)) (sub u (by simp)) (sub u⁻¹ (by simp))).trans ⟨fun hvis => ?_, fun hz => ?_⟩
  · by_contra hc
    obtain ⟨hPS, hP2'⟩ := not_or.1 hc
    obtain ⟨-, hZ, -⟩ := invisible_cyclic_space_u_multiplier_space_eq u hu P Q S₁ S₂ hcop hdeg hS₁ hS₂
      (not_not.1 hPS) (not_and_or.1 hP2')
    exact (u_multiplier_space_le_span_no_degree_one_no_visible_element u hu _ (sub u (by simp))
      (sub u⁻¹ (by simp)) fun f h1 h2 => (hZ f).1 ⟨h1, h2⟩).2 hvis
  · have hSP : ∀ k : ↥Qbar, S₁ ≠ C k * P := fun k hk => by
      subst hk
      have := drop (g₂ := aeval u Q * (aeval u Q * aeval u (C k * P) + aeval u P * aeval u S₂) /
        (u * aeval u P ^ 2)) (mem_H hu hP0 hQ2 k)
      omega
    rcases quadratic_fraction_extension_visible_element_mem_of_common_zero u hu P Q S₁
        hcop hdeg hS₁ hSP hz with h | h | ⟨a, ha, ha0, h⟩
    · exact Or.inl (hle h)
    · exact Or.inr (Or.inl (hle h))
    · exact Or.inr (Or.inr ⟨a, ha, ha0, hle h⟩)
