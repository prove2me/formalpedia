-- Prove2me | solution 1 for DiazModulus.conj_stable_circle_point_extension_no_two_by_three_configuration
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-06T07:49:22.053161+00:00
-- url     : https://prove2.me/submissions/2da779b0-8141-46f0-b9bf-ad5490bbbca1

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_circle_point_conjugate_pair_configuration_invisible_to_four_dimensional_extensions

open Complex ComplexConjugate

/-!
# No `2 × 3` configuration in `Q̄ + Q̄u + Q̄ū + Q̄ u/(u² − a)` when `a ā = ρ²`

Let `u ∉ Q̄` with `ρ = u ū` algebraic, and `a ∈ Q̄` non-zero with `a ā = ρ²`. Put
`z = u/(u² − a)²` and `w = u/(u² − a)`.

* `w ∈ W = Q̄ + Q̄u + Q̄ū + Q̄z + Q̄z̄`. With `ū = ρ/u` and `ρ² = a ā`, `ū² − ā = −ā(u² − a)/u²`,
  so `z̄ = (ρ/ā²)·u³/(u² − a)²` and `w = (ā²/ρ)·z̄ − a·z` (`div_mem_span`).
* `w ∉ Q̄ + Q̄u + Q̄ū`. From `w = c₀ + c₁u + c₂ū`, multiplying by `u(u² − a)` and using `uū = ρ`,
  `c₁u⁴ + c₀u³ + (c₂ρ − c₁a − 1)u² − c₀a u − c₂ρa = 0`. As `u` is transcendental over `Q̄`, every
  coefficient vanishes: `c₁ = 0`, then `c₂ = 0` (since `ρ a ≠ 0`), then `−1 = 0` (`div_not_mem`).

So `circle_point_conjugate_pair_configuration_invisible_to_four_dimensional_extensions` (second case, at `w`) excludes
a configuration in `Q̄ + Q̄u + Q̄ū + Q̄w`.
-/

namespace R5_conjStable

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

/-- `u² ≠ a` for `a ∈ Q̄`, as `u` is not a root of `X² − a`. -/
theorem sq_sub_ne_zero {u a : ℂ} (hu : u ∉ Qbar) (ha : a ∈ Qbar) : u ^ 2 - a ≠ 0 := by
  intro h
  obtain ⟨α, hα⟩ : ∃ α : ↥Qbar, algebraMap (↥Qbar) ℂ α = a := ⟨⟨a, ha⟩, rfl⟩
  have hP := aeval_eq_zero hu (P := X ^ 2 - C α) (by
    simp only [map_sub, map_pow, aeval_X, aeval_C, hα]
    exact h)
  have h2 := congrArg (coeff · 2) hP
  simp at h2

/-- Complex conjugation as a `ℚ`-algebra map. -/
noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

/-- Conjugation preserves algebraicity over `ℚ`, so it maps `Q̄` to itself. -/
theorem conj_mem_Qbar {a : ℂ} (ha : a ∈ Qbar) : conj a ∈ Qbar := by
  obtain ⟨p, hp0, hp⟩ := mem_Qbar_iff.1 ha
  refine mem_Qbar_iff.2 ⟨p, hp0, ?_⟩
  rw [show (conj a : ℂ) = cjQ a from rfl, Polynomial.aeval_algHom_apply, hp, map_zero]

theorem span_mul_mem {S : Set ℂ} {c v : ℂ} (hc : c ∈ Qbar) (hv : v ∈ Submodule.span Qbar S) :
    c * v ∈ Submodule.span Qbar S := by
  have := Submodule.smul_mem _ (⟨c, hc⟩ : ↥Qbar) hv
  rwa [Subfield.smul_def, smul_eq_mul] at this

theorem mem_span_three {u w : ℂ} (hw : w ∈ Submodule.span Qbar ({1, u, conj u} : Set ℂ)) :
    ∃ c₀ c₁ c₂ : ↥Qbar, w = algebraMap (↥Qbar) ℂ c₀ + algebraMap (↥Qbar) ℂ c₁ * u +
      algebraMap (↥Qbar) ℂ c₂ * conj u := by
  obtain ⟨c₀, c₁, c₂, rfl⟩ := Submodule.mem_span_triple.1 hw
  exact ⟨c₀, c₁, c₂, by simp only [Algebra.smul_def, mul_one]⟩

/-- `w = (ā²/ρ)·z̄ − a·z` for `w = u/(u² − a)`, `z = u/(u² − a)²`, `ρ = u ū`, when `a ā = ρ²`. -/
theorem div_mem_span {u a : ℂ} (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u))
    (ha : a ∈ Qbar) (haρ : a * conj a = (u * conj u) ^ 2) :
    u / (u ^ 2 - a) ∈ Submodule.span Qbar
      ({1, u, conj u, u / (u ^ 2 - a) ^ 2, conj (u / (u ^ 2 - a) ^ 2)} : Set ℂ) := by
  have hu0 := ne_zero_of_not_mem hu
  have hcu0 : conj u ≠ 0 := (_root_.map_ne_zero _).2 hu0
  have hd := sq_sub_ne_zero hu ha
  have hcd : conj u ^ 2 - conj a ≠ 0 := by
    have := (_root_.map_ne_zero (starRingEnd ℂ)).2 hd
    rwa [map_sub, map_pow] at this
  have e : u / (u ^ 2 - a) = conj a ^ 2 / (u * conj u) * conj (u / (u ^ 2 - a) ^ 2) +
      -a * (u / (u ^ 2 - a) ^ 2) := by
    rw [map_div₀, map_pow, map_sub, map_pow]
    field_simp
    linear_combination (-(u ^ 2 * conj u ^ 2 - 2 * u ^ 2 * conj a + a * conj a)) * haρ
  rw [e]
  exact add_mem
    (span_mul_mem (Qbar.div_mem (Qbar.pow_mem (conj_mem_Qbar ha) 2) (mem_Qbar_iff.2 hρ))
      (Submodule.subset_span (by simp)))
    (span_mul_mem (Qbar.neg_mem ha) (Submodule.subset_span (by simp)))

/-- `u/(u² − a) ∉ Q̄ + Q̄u + Q̄ū`. -/
theorem div_not_mem {u a : ℂ} (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u))
    (ha : a ∈ Qbar) (ha0 : a ≠ 0) :
    u / (u ^ 2 - a) ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) := by
  intro hw
  obtain ⟨c₀, c₁, c₂, e⟩ := mem_span_three hw
  have hd := sq_sub_ne_zero hu ha
  obtain ⟨ρ, hρ'⟩ : ∃ ρ : ↥Qbar, algebraMap (↥Qbar) ℂ ρ = u * conj u :=
    ⟨⟨u * conj u, mem_Qbar_iff.2 hρ⟩, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : ↥Qbar, algebraMap (↥Qbar) ℂ α = a := ⟨⟨a, ha⟩, rfl⟩
  have hdiv : (u ^ 2 - a) * (u / (u ^ 2 - a)) = u := by field_simp
  have hP := aeval_eq_zero hu (P := C c₁ * X ^ 4 + C c₀ * X ^ 3 +
      C (c₂ * ρ - c₁ * α - 1) * X ^ 2 - C (c₀ * α) * X - C (c₂ * ρ * α)) (by
    simp only [map_sub, map_add, map_mul, map_pow, map_one, aeval_X, aeval_C, hρ', hα]
    linear_combination (-(u * (u ^ 2 - a))) * e + u * hdiv)
  have hu0 := ne_zero_of_not_mem hu
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hρ'
    exact mul_ne_zero hu0 ((_root_.map_ne_zero _).2 hu0) hρ'.symm
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact ha0 (by rw [← hα, map_zero])
  have h4 := congrArg (coeff · 4) hP
  have h0 := congrArg (coeff · 0) hP
  have h2 := congrArg (coeff · 2) hP
  simp only [coeff_add, coeff_sub, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_zero] at h4 h0 h2
  norm_num at h4 h0 h2
  rw [h4, (h0.resolve_right hα0).resolve_right hρ0] at h2
  norm_num at h2

end R5_conjStable

open DiazModulus R5_conjStable in
theorem solution (u a : ℂ)
    (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u)) (ha : a ∈ Qbar) (ha0 : a ≠ 0)
    (haρ : a * conj a = (u * conj u) ^ 2) :
    ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, u / (u ^ 2 - a)} : Set ℂ) :=
  (circle_point_conjugate_pair_configuration_invisible_to_four_dimensional_extensions u a (u / (u ^ 2 - a) ^ 2)
    hu hρ ha ha0 (Or.inr ⟨haρ, rfl⟩)).2 _ (div_mem_span hu hρ ha haρ) (div_not_mem hu hρ ha ha0)

#print axioms solution
