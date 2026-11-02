-- Prove2me | solution 1 for DiazModulus.two_orbit_space_visible_to_four_dimensional_extensions_iff_common_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-01T09:25:33.033569+00:00
-- url     : https://prove2.me/submissions/59aa2aba-f14e-4b20-b99b-acd72208d5cc

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_visible_to_four_dimensional_extensions_iff_visible_element_mem
import Theorems.Thm_DiazModulus_quadratic_fraction_extension_visible_element_mem_of_common_zero
import Theorems.Thm_DiazModulus_invisible_two_orbit_space_u_multiplier_space_eq
import Theorems.Thm_DiazModulus_u_multiplier_space_le_span_no_degree_one_no_visible_element

open Complex ComplexConjugate

/-! # Visibility of a two-orbit space: iff a common zero on one of the two orbits

`W = span(1, u, u⁻¹, g₁, g₂)` with `g₁ = Q(u) S₁(u)/(u P(u))`, `g₂ = P(u) S₂(u)/(u Q(u))` and
`dim W = 5`. By `visible_to_four_dimensional_extensions_iff_visible_element_mem`, visibility of `W`
is "W contains a `t_x`".
* `⇐`: `dim W = 5` gives `S₁ ∉ Q̄·P` (else `g₁ = k Q(u)/u ∈ H₀` and `dim W ≤ 4`) and likewise
  `S₂ ∉ Q̄·Q`. A common zero of `P, S₁` (resp. `Q, S₂`) puts a `t_x` in `H₀ + Q̄g₁` (resp. `H₀ + Q̄g₂`)
  by `quadratic_fraction_extension_visible_element_mem_of_common_zero`, and these lie in `W`.
* `⇒`: with no common zero on either side, `invisible_two_orbit_space_u_multiplier_space_eq` gives
  `W ∩ u⁻¹W = span(1, u⁻¹)`, and `u_multiplier_space_le_span_no_degree_one_no_visible_element`
  excludes every `t_x`.
-/

namespace R21b_V3

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

end R21b_V3

open DiazModulus R21b_V3 in
open Polynomial in
theorem solution (u : ℂ) (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u))
    (P Q S₁ S₂ : (↥Qbar)[X]) (hcop : IsCoprime P Q) (hdeg : max P.natDegree Q.natDegree = 2) (hS₁ : S₁.natDegree ≤ 2) (hS₂ : S₂.natDegree ≤ 2)
    (h5 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u P * aeval u S₂ / (u * aeval u Q)} : Set ℂ)) = 5) :
    (∃ w ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u P * aeval u S₂ / (u * aeval u Q)} : Set ℂ), w ∉ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) ∧
        ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
          ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, u⁻¹, w} : Set ℂ)) ↔
    (¬ IsCoprime P S₁ ∨ (P.coeff 2 = 0 ∧ S₁.coeff 2 = 0)) ∨ (¬ IsCoprime Q S₂ ∨ (Q.coeff 2 = 0 ∧ S₂.coeff 2 = 0)) := by
  have hP0 : P ≠ 0 := ne_zero_of_coprime hcop.symm (by rwa [max_comm])
  have hQ0 : Q ≠ 0 := ne_zero_of_coprime hcop hdeg
  have hP2 : P.natDegree ≤ 2 := hdeg ▸ le_max_left _ _
  have hQ2 : Q.natDegree ≤ 2 := hdeg ▸ le_max_right _ _
  have sub : ∀ x ∈ ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
      aeval u P * aeval u S₂ / (u * aeval u Q)} : Set ℂ), x ∈ Submodule.span Qbar ({1, u, u⁻¹,
      aeval u Q * aeval u S₁ / (u * aeval u P), aeval u P * aeval u S₂ / (u * aeval u Q)} : Set ℂ) :=
    fun x hx => Submodule.subset_span hx
  have sub4 : ∀ g ∈ ({aeval u Q * aeval u S₁ / (u * aeval u P),
      aeval u P * aeval u S₂ / (u * aeval u Q)} : Set ℂ),
      Submodule.span Qbar ({1, u, u⁻¹, g} : Set ℂ) ≤ Submodule.span Qbar ({1, u, u⁻¹,
        aeval u Q * aeval u S₁ / (u * aeval u P), aeval u P * aeval u S₂ / (u * aeval u Q)} : Set ℂ) :=
    fun g hg => Submodule.span_mono (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hg ⊢
      rcases hg with rfl | rfl <;> tauto)
  have hPT {g : ℂ} (hg : g ∈ ({aeval u Q * aeval u S₁ / (u * aeval u P),
      aeval u P * aeval u S₂ / (u * aeval u Q)} : Set ℂ))
      (h : u ^ 2 ∈ Submodule.span Qbar ({1, u, u⁻¹, g} : Set ℂ) ∨
        (u ^ 2)⁻¹ ∈ Submodule.span Qbar ({1, u, u⁻¹, g} : Set ℂ) ∨
        ∃ a ∈ Qbar, a ≠ 0 ∧ (u - a)⁻¹ ∈ Submodule.span Qbar ({1, u, u⁻¹, g} : Set ℂ)) :
      u ^ 2 ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
          aeval u P * aeval u S₂ / (u * aeval u Q)} : Set ℂ) ∨ (u ^ 2)⁻¹ ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
          aeval u P * aeval u S₂ / (u * aeval u Q)} : Set ℂ) ∨
        ∃ a ∈ Qbar, a ≠ 0 ∧ (u - a)⁻¹ ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
          aeval u P * aeval u S₂ / (u * aeval u Q)} : Set ℂ) := by
    rcases h with h | h | ⟨a, ha, ha0, h⟩
    exacts [Or.inl (sub4 g hg h), Or.inr (Or.inl (sub4 g hg h)), Or.inr (Or.inr ⟨a, ha, ha0, sub4 g hg h⟩)]
  refine (visible_to_four_dimensional_extensions_iff_visible_element_mem u hu hρ _
    (sub 1 (by simp)) (sub u (by simp)) (sub u⁻¹ (by simp))).trans ⟨fun hvis => ?_, fun hz => ?_⟩
  · by_contra hc
    obtain ⟨hA, hB⟩ := not_or.1 hc
    obtain ⟨hPS, hP2'⟩ := not_or.1 hA
    obtain ⟨hQS, hQ2'⟩ := not_or.1 hB
    obtain ⟨-, hZ, -⟩ := invisible_two_orbit_space_u_multiplier_space_eq u hu P Q S₁ S₂ hcop hdeg hS₁ hS₂
      (not_not.1 hPS) (not_not.1 hQS) (not_and_or.1 hP2') (not_and_or.1 hQ2')
    exact (u_multiplier_space_le_span_no_degree_one_no_visible_element u hu _ (sub u (by simp))
      (sub u⁻¹ (by simp)) fun f h1 h2 => (hZ f).1 ⟨h1, h2⟩).2 hvis
  · rcases hz with hA | hB
    · refine hPT (by simp) (quadratic_fraction_extension_visible_element_mem_of_common_zero u hu P Q S₁
        hcop hdeg hS₁ (fun k hk => ?_) hA)
      subst hk
      have := drop (g₂ := aeval u P * aeval u S₂ / (u * aeval u Q)) (mem_H hu hP0 hQ2 k)
      omega
    · refine hPT (by simp) (quadratic_fraction_extension_visible_element_mem_of_common_zero u hu Q P S₂
        hcop.symm (by rwa [max_comm]) hS₂ (fun k hk => ?_) hB)
      subst hk
      rw [Set.pair_comm] at h5
      have := drop (g₂ := aeval u Q * aeval u S₁ / (u * aeval u P)) (mem_H hu hQ0 hP2 k)
      omega
