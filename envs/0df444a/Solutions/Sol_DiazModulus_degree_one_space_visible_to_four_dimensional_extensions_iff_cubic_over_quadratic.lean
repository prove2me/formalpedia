-- Prove2me | solution 1 for DiazModulus.degree_one_space_visible_to_four_dimensional_extensions_iff_cubic_over_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T09:49:59.681555+00:00
-- url     : https://prove2.me/submissions/4bd63c92-a863-4a66-a0c3-fb89dbc8ab68

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_degree_one_space_cubic_over_quadratic_of_mem_square_or_reciprocal
import Theorems.Thm_DiazModulus_degree_one_space_mem_square_or_reciprocal_of_cubic_over_quadratic
import Theorems.Thm_DiazModulus_circle_point_extension_two_by_three_configuration_iff

open Complex ComplexConjugate

/-! # Degree-one spaces: visible to the four-dimensional extensions exactly when complete

Let `u ∉ Q̄` with `ρ = u ū` algebraic, `H₀ = span_Q̄ {1, u, ū}` and `W = span_Q̄ {1, u, ū, g, ug}`.
Call `t` a Theorem B element if `t = u²`, `t = ū²` or `t = (u − a)⁻¹` with `a ∈ Q̄ \ {0}`.

* (⇒) Let `w ∈ W \ H₀` with a `2 × 3` configuration in `H₀ + Q̄w`. Theorem B
  (`circle_point_extension_two_by_three_configuration_iff`) puts `w` in `H₀ + Q̄t` for a Theorem B
  element `t`. As `w ∉ H₀`, exchange puts `t` in `H₀ + Q̄w ⊆ W`, and
  `degree_one_space_cubic_over_quadratic_of_mem_square_or_reciprocal` makes `g` cubic over
  quadratic: `u R(u) g = N(u)` with `R ≠ 0`, `deg R ≤ 2`, `deg N ≤ 3`.
* (⇐) `degree_one_space_mem_square_or_reciprocal_of_cubic_over_quadratic` puts a Theorem B element
  `t` in `W`. It is not in `H₀`: with `ū = ρ/u`, each of `t = c₁ + c₂u + c₃ū` clears to a non-zero
  polynomial over `Q̄` vanishing at the transcendental `u` (leading coefficient `1`, constant term
  `−ρ²`, or value `−a` at `a`). So `w = t` works, by the "if" half of Theorem B.
-/

namespace R17_vis1

open DiazModulus Polynomial

theorem set_eq_insert (u w : ℂ) : ({1, u, conj u, w} : Set ℂ) = insert w {1, u, conj u} := by
  ext t
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- Exchange: `w ∉ H₀` and `w ∈ H₀ + Q̄t` give `t ∈ H₀ + Q̄w`. -/
theorem exchange {u t w : ℂ} (hw : w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ))
    (h : w ∈ Submodule.span Qbar ({1, u, conj u, t} : Set ℂ)) :
    t ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) := by
  rw [set_eq_insert] at h ⊢
  exact mem_span_insert_exchange h hw

/-- `H₀ + Q̄w ≤ W` for `w ∈ W`. -/
theorem span_four_le {u w f g : ℂ}
    (hw : w ∈ Submodule.span Qbar ({1, u, conj u, f, g} : Set ℂ)) :
    Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) ≤
      Submodule.span Qbar ({1, u, conj u, f, g} : Set ℂ) := by
  refine Submodule.span_le.2 fun x hx => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact Submodule.subset_span (by simp)
  · exact Submodule.subset_span (by simp)
  · exact Submodule.subset_span (by simp)
  · exact hw

/-- Outside `Q̄`, no non-zero polynomial over `Q̄` vanishes. -/
theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) :
    P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem coeffs3 {u cu w : ℂ} (hw : w ∈ Submodule.span Qbar ({1, u, cu} : Set ℂ)) :
    ∃ c₁ c₂ c₃ : ↥Qbar, w = (c₁ : ℂ) + c₂ * u + c₃ * cu := by
  obtain ⟨c₁, w₁, hw₁, rfl⟩ := Submodule.mem_span_insert.1 hw
  obtain ⟨c₂, w₂, hw₂, rfl⟩ := Submodule.mem_span_insert.1 hw₁
  obtain ⟨c₃, rfl⟩ := Submodule.mem_span_singleton.1 hw₂
  exact ⟨c₁, c₂, c₃, by simp only [Subfield.smul_def, smul_eq_mul]; ring⟩

theorem red_sq {u cu : ℂ} (hu : u ∉ Qbar) {ρ a₁ a₂ a₃ : ↥Qbar} (hcuu : cu * u = ρ)
    (h : u ^ 2 = a₁ + a₂ * u + a₃ * cu) : False := by
  have hP := aeval_eq_zero hu (P := X ^ 3 - C a₂ * X ^ 2 - C a₁ * X - C (a₃ * ρ))
    (by
      simp only [map_sub, map_mul, map_pow, aeval_C, aeval_X, am]
      linear_combination u * h + a₃ * hcuu)
  have := congrArg (coeff · 3) hP
  simp [coeff_X_pow] at this

theorem red_csq {u cu : ℂ} (hu : u ∉ Qbar) {ρ a₁ a₂ a₃ : ↥Qbar} (hρ : ρ ≠ 0)
    (hcuu : cu * u = ρ) (h : cu ^ 2 = a₁ + a₂ * u + a₃ * cu) : False := by
  have hP := aeval_eq_zero hu
    (P := C a₂ * X ^ 3 + C a₁ * X ^ 2 + C (a₃ * ρ) * X - C (ρ * ρ))
    (by
      simp only [map_sub, map_add, map_mul, map_pow, aeval_C, aeval_X, am]
      linear_combination (-u ^ 2) * h + (cu * u + ρ - a₃ * u) * hcuu)
  have := congrArg (coeff · 0) hP
  simp [coeff_X, coeff_C, coeff_X_pow, hρ] at this

theorem red_inv {u cu : ℂ} (hu : u ∉ Qbar) {ρ a₁ a₂ a₃ β : ↥Qbar} (hβ : β ≠ 0)
    (hcuu : cu * u = ρ) (h : (u - β)⁻¹ = a₁ + a₂ * u + a₃ * cu) : False := by
  have hub : (u - β) * (u - β)⁻¹ = 1 :=
    mul_inv_cancel₀ (sub_ne_zero.2 fun e => hu (by rw [e]; exact β.2))
  have hP := aeval_eq_zero hu
    (P := (X - C β) * (C a₁ * X + C a₂ * X ^ 2 + C (a₃ * ρ)) - X)
    (by
      simp only [map_sub, map_add, map_mul, map_pow, aeval_C, aeval_X, am]
      linear_combination (-u * (u - β)) * h + u * hub - (u - β) * a₃ * hcuu)
  have := congrArg (eval β) hP
  simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X, sub_self, zero_mul,
    zero_sub, eval_zero, neg_eq_zero] at this
  exact hβ this

end R17_vis1

open DiazModulus R17_vis1 Polynomial in
theorem solution
    (u g : ℂ) (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u))
    (hind : LinearIndependent (↥Qbar) ![1, u, conj u, g, u * g]) :
    (∃ w ∈ Submodule.span Qbar ({1, u, conj u, g, u * g} : Set ℂ), w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) ∧
        ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
          ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ)) ↔
      ∃ R N : (↥Qbar)[X], R ≠ 0 ∧ R.natDegree ≤ 2 ∧ N.natDegree ≤ 3 ∧ u * aeval u R * g = aeval u N := by
  constructor
  · rintro ⟨w, hw, hw0, hconf⟩
    have hle := span_four_le hw
    apply DiazModulus.degree_one_space_cubic_over_quadratic_of_mem_square_or_reciprocal u g hu hρ
    rcases (DiazModulus.circle_point_extension_two_by_three_configuration_iff u w hu hρ hw0).1
      hconf with h | h | ⟨a, ha, ha0, h⟩
    · exact Or.inl (hle (exchange hw0 h))
    · exact Or.inr (Or.inl (hle (exchange hw0 h)))
    · exact Or.inr (Or.inr ⟨a, ha, ha0, hle (exchange hw0 h)⟩)
  · rintro ⟨R, N, hR, hRd, hNd, hRN⟩
    have hu0 : u ≠ 0 := fun h => hu (h ▸ Subfield.zero_mem _)
    set ρ : ↥Qbar := ⟨u * conj u, mem_Qbar_iff.2 hρ⟩ with hρdef
    have hcuu : conj u * u = ρ := by rw [hρdef, mul_comm]
    have hρ0 : ρ ≠ 0 := by
      intro e
      have : (ρ : ℂ) = 0 := by rw [e]; rfl
      exact mul_ne_zero hu0 ((_root_.map_ne_zero _).2 hu0) this
    -- a Theorem B element `t ∈ W \ H₀` gives the visible `w = t`
    have key : ∀ t, t ∈ Submodule.span Qbar ({1, u, conj u, g, u * g} : Set ℂ) →
        t ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) →
        t ∈ Submodule.span Qbar ({1, u, conj u, u ^ 2} : Set ℂ) ∨
          t ∈ Submodule.span Qbar ({1, u, conj u, conj u ^ 2} : Set ℂ) ∨
          (∃ a ∈ Qbar, a ≠ 0 ∧ t ∈ Submodule.span Qbar ({1, u, conj u, (u - a)⁻¹} : Set ℂ)) →
        ∃ w ∈ Submodule.span Qbar ({1, u, conj u, g, u * g} : Set ℂ),
          w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) ∧
          ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧
            LinearIndependent (↥Qbar) y ∧
            ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) :=
      fun t ht ht0 hB => ⟨t, ht, ht0,
        (DiazModulus.circle_point_extension_two_by_three_configuration_iff u t hu hρ ht0).2 hB⟩
    rcases DiazModulus.degree_one_space_mem_square_or_reciprocal_of_cubic_over_quadratic u g hu hρ
      hind R N hR hRd hNd hRN with h | h | ⟨a, ha, ha0, h⟩
    · refine key _ h (fun h0 => ?_) (Or.inl (Submodule.subset_span (by simp)))
      obtain ⟨c₁, c₂, c₃, e⟩ := coeffs3 h0
      exact red_sq hu hcuu e
    · refine key _ h (fun h0 => ?_) (Or.inr (Or.inl (Submodule.subset_span (by simp))))
      obtain ⟨c₁, c₂, c₃, e⟩ := coeffs3 h0
      exact red_csq hu hρ0 hcuu e
    · refine key _ h (fun h0 => ?_) (Or.inr (Or.inr ⟨a, ha, ha0, Submodule.subset_span (by simp)⟩))
      obtain ⟨c₁, c₂, c₃, e⟩ := coeffs3 h0
      have hβ : (⟨a, ha⟩ : ↥Qbar) ≠ 0 := fun e' => ha0 (congrArg Subtype.val e')
      exact red_inv (β := ⟨a, ha⟩) hu hβ hcuu e
