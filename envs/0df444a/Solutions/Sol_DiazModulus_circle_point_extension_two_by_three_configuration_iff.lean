-- Prove2me | solution 1 for DiazModulus.circle_point_extension_two_by_three_configuration_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-05T07:56:25.314473+00:00
-- url     : https://prove2.me/submissions/89de4b46-8cd0-48e5-a8a9-5ad3d0a87018

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_two_by_three_configuration_forces_progression
import Theorems.Thm_DiazModulus_circle_hull_progression_contains_square_or_reciprocal
import Theorems.Thm_DiazModulus_circle_point_extension_carries_two_by_three_configuration

open Complex ComplexConjugate

/-!
# The extensions of `Q̄ + Q̄u + Q̄ū` that carry a `2 × 3` configuration

Let `u ∉ Q̄` with `ρ = u ū` algebraic, `S = Q̄ + Q̄u + Q̄ū` and `z ∉ S`. Then `V = S + Q̄z` contains
the six products `xᵢyⱼ` of some `Q̄`-free `x ∈ ℂ²`, `y ∈ ℂ³` exactly when `z ∈ S + Q̄w` (that is,
`V = S + Q̄w`) with `w = u²`, `w = ū²` or `w = 1/(u − a)` for a non-zero `a ∈ Q̄`.

* **(⇐)** Exchange: `z ∈ S + Q̄w` and `z ∉ S` give `w ∈ V`, so the configuration carried by
  `S + Q̄w ≤ V` (`circle_point_extension_carries_two_by_three_configuration`) lies in `V`.
* **(⇒)** `V = b (Q̄ + Q̄h + Q̄h² + Q̄h³)` with `h ∉ Q̄`
  (`two_by_three_configuration_forces_progression`), and such a progression through `1, u, ū`
  contains `u²`, `ū²` or some `1/(u − a)` (`circle_hull_progression_contains_square_or_reciprocal`).
  Each such `w` is outside `S` (else `u` is a root of a non-zero polynomial of degree at most `3`
  over `Q̄`), and exchange gives `z ∈ S + Q̄w`.
-/

namespace R4B_main

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

theorem mem_span_three {u w : ℂ} (hw : w ∈ Submodule.span Qbar ({1, u, conj u} : Set ℂ)) :
    ∃ c₀ c₁ c₂ : ↥Qbar, w = algebraMap (↥Qbar) ℂ c₀ + algebraMap (↥Qbar) ℂ c₁ * u +
      algebraMap (↥Qbar) ℂ c₂ * conj u := by
  obtain ⟨c₀, c₁, c₂, rfl⟩ := Submodule.mem_span_triple.1 hw
  exact ⟨c₀, c₁, c₂, by simp only [Algebra.smul_def, mul_one]⟩

/-! ## The three points are outside `S` -/

theorem sq_not_mem {u : ℂ} (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u)) :
    u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) := by
  intro hw
  obtain ⟨c₀, c₁, c₂, e⟩ := mem_span_three hw
  obtain ⟨ρ, -, hρ'⟩ := exists_rho hu hρ
  have hP := aeval_eq_zero hu (P := X ^ 3 - C c₁ * X ^ 2 - C c₀ * X - C c₂ * C ρ) (by
    simp only [map_sub, map_mul, map_pow, aeval_X, aeval_C, hρ']
    linear_combination u * e)
  have h3 := congrArg (coeff · 3) hP
  simp at h3

theorem conj_sq_not_mem {u : ℂ} (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u)) :
    conj u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) := by
  intro hw
  obtain ⟨c₀, c₁, c₂, e⟩ := mem_span_three hw
  obtain ⟨ρ, hρ0, hρ'⟩ := exists_rho hu hρ
  have hP := aeval_eq_zero hu
    (P := C c₁ * X ^ 3 + C c₀ * X ^ 2 + C c₂ * C ρ * X - C (ρ ^ 2)) (by
    simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, hρ']
    linear_combination (-u ^ 2) * e)
  have h0 := congrArg (eval 0) hP
  simp [hρ0] at h0

theorem inv_not_mem {u a : ℂ} (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u))
    (ha : a ∈ Qbar) (ha0 : a ≠ 0) :
    (u - a)⁻¹ ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) := by
  intro hw
  obtain ⟨c₀, c₁, c₂, e⟩ := mem_span_three hw
  obtain ⟨ρ, -, hρ'⟩ := exists_rho hu hρ
  have hua : u - a ≠ 0 := fun h => hu (sub_eq_zero.1 h ▸ ha)
  obtain ⟨α, hα⟩ : ∃ α : ↥Qbar, algebraMap (↥Qbar) ℂ α = a := ⟨⟨a, ha⟩, rfl⟩
  have hP := aeval_eq_zero hu
    (P := (X - C α) * (C c₀ * X + C c₁ * X ^ 2 + C c₂ * C ρ) - X) (by
    simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, hρ', hα]
    linear_combination (-(u * (u - a))) * e + u * mul_inv_cancel₀ hua)
  have h := congrArg (eval α) hP
  simp only [eval_sub, eval_mul, eval_X, eval_C, sub_self, zero_mul, zero_sub, eval_zero,
    neg_eq_zero] at h
  exact ha0 (by rw [← hα, h, map_zero])

/-! ## Exchange -/

theorem set_eq_insert (u w : ℂ) : ({1, u, conj u, w} : Set ℂ) = insert w {1, u, conj u} := by
  ext t
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem exchange {u z w : ℂ} (hw : w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ))
    (h : w ∈ Submodule.span Qbar ({1, u, conj u, z} : Set ℂ)) :
    z ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) := by
  rw [set_eq_insert] at h ⊢
  exact mem_span_insert_exchange h hw

theorem span_le_of_mem {u z w : ℂ} (h : w ∈ Submodule.span Qbar ({1, u, conj u, z} : Set ℂ)) :
    Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) ≤
      Submodule.span Qbar ({1, u, conj u, z} : Set ℂ) := by
  rw [set_eq_insert u w, Submodule.span_insert, set_eq_insert u z]
  exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 (by rwa [set_eq_insert] at h))
    (Submodule.span_mono (Set.subset_insert _ _))

/-- **(⇒)**: a configuration in `V` puts `u²`, `ū²` or some `1/(u − a)` in `V`. -/
theorem forward {u z : ℂ} (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u))
    {x : Fin 2 → ℂ} {y : Fin 3 → ℂ} (hx : LinearIndependent (↥Qbar) x)
    (hy : LinearIndependent (↥Qbar) y)
    (hxy : ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, z} : Set ℂ)) :
    u ^ 2 ∈ Submodule.span Qbar ({1, u, conj u, z} : Set ℂ) ∨
      conj u ^ 2 ∈ Submodule.span Qbar ({1, u, conj u, z} : Set ℂ) ∨
      ∃ a ∈ Qbar, a ≠ 0 ∧ (u - a)⁻¹ ∈ Submodule.span Qbar ({1, u, conj u, z} : Set ℂ) := by
  have : FiniteDimensional (↥Qbar) (Submodule.span Qbar ({1, u, conj u, z} : Set ℂ)) :=
    FiniteDimensional.span_of_finite _ (Set.toFinite _)
  have hV4 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, conj u, z} : Set ℂ)) ≤ 4 := by
    have h := finrank_span_finset_le_card (R := ↥Qbar) ({1, u, conj u, z} : Finset ℂ)
    have e : ((({1, u, conj u, z} : Finset ℂ)) : Set ℂ) = {1, u, conj u, z} := by simp
    rw [e] at h
    exact h.trans Finset.card_le_four
  obtain ⟨b, h, hb, hh, hV⟩ := two_by_three_configuration_forces_progression
    (Submodule.span Qbar ({1, u, conj u, z} : Set ℂ)) hV4 x y hx hy hxy
  exact circle_hull_progression_contains_square_or_reciprocal u b h _ hu hρ hb hh hV
    (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
    (Submodule.subset_span (by simp))

end R4B_main

open DiazModulus R4B_main in
theorem solution (u z : ℂ) (hu : u ∉ Qbar)
    (hρ : IsAlgebraic ℚ (u * conj u))
    (hz : z ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ)) :
    (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
        ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, z} : Set ℂ)) ↔
      (z ∈ Submodule.span Qbar ({1, u, conj u, u ^ 2} : Set ℂ) ∨
        z ∈ Submodule.span Qbar ({1, u, conj u, conj u ^ 2} : Set ℂ) ∨
        ∃ a ∈ Qbar, a ≠ 0 ∧ z ∈ Submodule.span Qbar ({1, u, conj u, (u - a)⁻¹} : Set ℂ)) := by
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    rcases forward hu hρ hx hy hxy with hw | hw | ⟨a, ha, ha0, hw⟩
    · exact Or.inl (exchange (sq_not_mem hu hρ) hw)
    · exact Or.inr (Or.inl (exchange (conj_sq_not_mem hu hρ) hw))
    · exact Or.inr (Or.inr ⟨a, ha, ha0, exchange (inv_not_mem hu hρ ha ha0) hw⟩)
  · intro hzw
    obtain ⟨w, hw, hzw⟩ : ∃ w : ℂ,
        (w = u ^ 2 ∨ w = conj u ^ 2 ∨ ∃ a ∈ Qbar, a ≠ 0 ∧ w = (u - a)⁻¹) ∧
          z ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) := by
      rcases hzw with hzw | hzw | ⟨a, ha, ha0, hzw⟩
      · exact ⟨_, Or.inl rfl, hzw⟩
      · exact ⟨_, Or.inr (Or.inl rfl), hzw⟩
      · exact ⟨_, Or.inr (Or.inr ⟨a, ha, ha0, rfl⟩), hzw⟩
    obtain ⟨x, y, hx, hy, hxy⟩ :=
      circle_point_extension_carries_two_by_three_configuration u w hu hρ hw
    exact ⟨x, y, hx, hy, fun i j => span_le_of_mem (exchange hz hzw) (hxy i j)⟩

#print axioms solution
