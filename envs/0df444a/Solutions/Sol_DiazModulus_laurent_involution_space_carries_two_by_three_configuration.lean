-- Prove2me | solution 1 for DiazModulus.laurent_involution_space_carries_two_by_three_configuration
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T14:43:48.434193+00:00
-- url     : https://prove2.me/submissions/4b8cf33d-d158-468d-8a53-e7dab86c5cd2

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The involution normal form carries a `2 × 3` configuration

Let `v ∉ Q̄` with `v v̄ = 1`, and `e, β, ζ ∈ Q̄` arbitrary. In
`W = span_Q̄ {1, v, v̄, v̄² + e v², β v̄³ + ζ v² + e v³}` the families `x = (1, v + β v̄)` and
`y = (1, v̄ + eβ v, v̄² + ζ v + e v²)` form a configuration.
Using only `v v̄ = 1`, the six products are `1`, `v̄ + eβ v`, `(v̄² + e v²) + ζ v`, `v + β v̄`,
`β (v̄² + e v²) + (1 + eβ²)` and `(β v̄³ + ζ v² + e v³) + v̄ + βζ + eβ v`, each an explicit
`Q̄`-combination of the five generators.
Freeness: multiplied by `v` (for `x`) or by `v²` (for `y`), a `Q̄`-relation becomes a polynomial
identity of degree at most `4` at the transcendental `v`. For `x` its coefficients are `tβ, s, t`;
for `y` the coefficients of `1, v, v²` are the three coefficients of the relation (the orders
`0, -1, -2` are distinct).
-/

namespace R18_C5

open DiazModulus Polynomial

/-- Outside `Q̄`, no non-zero polynomial over `Q̄` vanishes. -/
theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) :
    P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

/-- A polynomial relation of degree `4` over `Q̄` at `u ∉ Q̄` is trivial. -/
theorem five_terms {u : ℂ} (hu : u ∉ Qbar) {a₀ a₁ a₂ a₃ a₄ : ↥Qbar}
    (h : (a₀ : ℂ) + a₁ * u + a₂ * u ^ 2 + a₃ * u ^ 3 + a₄ * u ^ 4 = 0) :
    a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 ∧ a₄ = 0 := by
  have hP := aeval_eq_zero hu (P := C a₀ + C a₁ * X + C a₂ * X ^ 2 + C a₃ * X ^ 3 + C a₄ * X ^ 4)
    (by simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, am]; exact h)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 0) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 1) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 2) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 3) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 4) hP

/-- Membership in `W` from an explicit combination of its five generators. -/
theorem mem_W {u t z zc w : ℂ} (c₁ c₂ c₃ c₄ c₅ : ↥Qbar)
    (h : w = (c₁ : ℂ) + c₂ * u + c₃ * t + c₄ * z + c₅ * zc) :
    w ∈ Submodule.span Qbar ({1, u, t, z, zc} : Set ℂ) := by
  have hs : ∀ v ∈ ({1, u, t, z, zc} : Set ℂ), ∀ c : ↥Qbar,
      (c : ℂ) * v ∈ Submodule.span Qbar ({1, u, t, z, zc} : Set ℂ) := fun v hv c => by
    rw [← smul_eq_mul, ← Subfield.smul_def]
    exact Submodule.smul_mem _ c (Submodule.subset_span hv)
  rw [h]
  refine add_mem (add_mem (add_mem (add_mem ?_ (hs u (by simp) c₂)) (hs t (by simp) c₃))
    (hs z (by simp) c₄)) (hs zc (by simp) c₅)
  simpa using hs 1 (by simp) c₁

theorem config_of {W : Submodule (↥Qbar) ℂ} {x₀ x₁ y₀ y₁ y₂ : ℂ}
    (h00 : x₀ * y₀ ∈ W) (h01 : x₀ * y₁ ∈ W) (h02 : x₀ * y₂ ∈ W) (h10 : x₁ * y₀ ∈ W)
    (h11 : x₁ * y₁ ∈ W) (h12 : x₁ * y₂ ∈ W) : ∀ i j, ![x₀, x₁] i * ![y₀, y₁, y₂] j ∈ W := by
  intro i j
  fin_cases i <;> fin_cases j <;> simpa

theorem li_three {v₀ v₁ v₂ : ℂ}
    (h : ∀ g₀ g₁ g₂ : ↥Qbar, (g₀ : ℂ) * v₀ + g₁ * v₁ + g₂ * v₂ = 0 → g₀ = 0 ∧ g₁ = 0 ∧ g₂ = 0) :
    LinearIndependent (↥Qbar) ![v₀, v₁, v₂] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Subfield.smul_def] at hg
  obtain ⟨h0, h1, h2⟩ := h (g 0) (g 1) (g 2) (by simpa using hg)
  intro i
  fin_cases i
  exacts [h0, h1, h2]

end R18_C5

open DiazModulus R18_C5 in
theorem solution
    (v : ℂ) (hv : v ∉ Qbar) (hv1 : v * conj v = 1)
    (e β ζ : ℂ) (he : e ∈ Qbar) (hβ : β ∈ Qbar) (hζ : ζ ∈ Qbar) :
    LinearIndependent (↥Qbar) ![1, v + β * conj v] ∧
      LinearIndependent (↥Qbar) ![1, conj v + e * β * v, conj v ^ 2 + ζ * v + e * v ^ 2] ∧
      ∀ i j, ![1, v + β * conj v] i * ![1, conj v + e * β * v, conj v ^ 2 + ζ * v + e * v ^ 2] j ∈
        Submodule.span Qbar ({1, v, conj v, conj v ^ 2 + e * v ^ 2, β * conj v ^ 3 + ζ * v ^ 2 + e * v ^ 3} : Set ℂ) := by
  obtain ⟨e, rfl⟩ : ∃ e' : ↥Qbar, (e' : ℂ) = e := ⟨⟨e, he⟩, rfl⟩
  obtain ⟨β, rfl⟩ : ∃ b : ↥Qbar, (b : ℂ) = β := ⟨⟨β, hβ⟩, rfl⟩
  obtain ⟨ζ, rfl⟩ : ∃ z : ↥Qbar, (z : ℂ) = ζ := ⟨⟨ζ, hζ⟩, rfl⟩
  refine ⟨LinearIndependent.pair_iff.2 fun s t hst => ?_, li_three fun g₀ g₁ g₂ hg => ?_,
    config_of ?_ ?_ ?_ ?_ ?_ ?_⟩
  · simp only [Subfield.smul_def, smul_eq_mul] at hst
    obtain ⟨h0, h1, h2, -⟩ := five_terms hv (a₀ := t * β) (a₁ := s) (a₂ := t) (a₃ := 0) (a₄ := 0)
      (by push_cast; linear_combination v * hst - (t : ℂ) * β * hv1)
    exact ⟨h1, h2⟩
  · obtain ⟨h0, h1, h2, -⟩ := five_terms hv (a₀ := g₂) (a₁ := g₁) (a₂ := g₀)
      (a₃ := g₁ * e * β + g₂ * ζ) (a₄ := g₂ * e)
      (by push_cast; linear_combination v ^ 2 * hg - ((g₁ : ℂ) * v + g₂ * (v * conj v + 1)) * hv1)
    exact ⟨h2, h1, h0⟩
  · exact mem_W 1 0 0 0 0 (by push_cast; ring)
  · exact mem_W 0 (e * β) 1 0 0 (by push_cast; ring)
  · exact mem_W 0 ζ 0 1 0 (by push_cast; ring)
  · exact mem_W 0 1 β 0 0 (by push_cast; ring)
  · exact mem_W (1 + e * β ^ 2) 0 0 β 0 (by push_cast; linear_combination (1 + (e : ℂ) * β ^ 2) * hv1)
  · exact mem_W (β * ζ) (e * β) 1 0 1
      (by push_cast; linear_combination (conj v + (β : ℂ) * ζ + e * β * v) * hv1)
