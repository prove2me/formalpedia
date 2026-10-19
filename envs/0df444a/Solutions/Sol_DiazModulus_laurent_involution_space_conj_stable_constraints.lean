-- Prove2me | solution 1 for DiazModulus.laurent_involution_space_conj_stable_constraints
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T14:46:35.079964+00:00
-- url     : https://prove2.me/submissions/23141532-931d-4303-b848-b4dd42472a8b

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # Conjugation-stability of the involution space forces |e| = |β| = 1 and ζ = −β e² ζ̄

Let `S = span(1, v, v̄, n₀, n₁)` with `n₀ = v̄² + e v²` and `n₁ = β v̄³ + ζ v² + e v³`, where
`v v̄ = 1`, `v ∉ Q̄` and `β ≠ 0`. Conjugation fixes `S`, so `n̄₀ = v² + ē v̄²` and
`n̄₁ = β̄ v³ + ζ̄ v̄² + ē v̄³` are `Q̄`-combinations of `1, v, v̄, n₀, n₁`. Multiplying each relation
by `v³` and using `v̄ v = 1` gives a polynomial relation of degree `6` in `v`, which is trivial
since `v` is transcendental over `Q̄`; so we may compare coefficients.
* For `n̄₀ = c₁ + c₂ v + c₃ v̄ + c₄ n₀ + c₅ n₁`: the `v⁻³` coefficient gives `c₅ β = 0`, so `c₅ = 0`;
  the `v⁻²` coefficient gives `c₄ = ē`; the `v²` coefficient gives `1 = c₄ e`, so `e ē = 1`.
* For `n̄₁ = d₁ + d₂ v + d₃ v̄ + d₄ n₀ + d₅ n₁`: the `v⁻³` and `v³` coefficients give `ē = d₅ β`
  and `β̄ = d₅ e`, so `β β̄ = d₅ β e = e ē = 1`; the `v⁻²` coefficient gives `d₄ = ζ̄`, and the
  `v²` coefficient gives `d₄ e + d₅ ζ = 0`. Multiplying the last one by `β e` gives
  `β e² ζ̄ + ζ = 0`.
-/

namespace R18_C4

open DiazModulus Polynomial

/-- Outside `Q̄`, no non-zero polynomial over `Q̄` vanishes. -/
theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) :
    P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

/-- A polynomial relation of degree `6` over `Q̄` at `u ∉ Q̄` is trivial. -/
theorem seven_terms {u : ℂ} (hu : u ∉ Qbar) {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : ↥Qbar}
    (h : (a₀ : ℂ) + a₁ * u + a₂ * u ^ 2 + a₃ * u ^ 3 + a₄ * u ^ 4 + a₅ * u ^ 5 +
      a₆ * u ^ 6 = 0) :
    a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 ∧ a₄ = 0 ∧ a₅ = 0 ∧ a₆ = 0 := by
  have hP := aeval_eq_zero hu (P := C a₀ + C a₁ * X + C a₂ * X ^ 2 + C a₃ * X ^ 3 +
    C a₄ * X ^ 4 + C a₅ * X ^ 5 + C a₆ * X ^ 6)
    (by simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, am]; exact h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 0) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 1) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 2) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 3) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 4) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 5) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 6) hP

theorem coeffs {u z zc t w : ℂ} (hw : w ∈ Submodule.span Qbar ({1, u, t, z, zc} : Set ℂ)) :
    ∃ c₁ c₂ c₃ c₄ c₅ : ↥Qbar, w = (c₁ : ℂ) + c₂ * u + c₃ * t + c₄ * z + c₅ * zc := by
  obtain ⟨c₁, w₁, hw₁, rfl⟩ := Submodule.mem_span_insert.1 hw
  obtain ⟨c₂, w₂, hw₂, rfl⟩ := Submodule.mem_span_insert.1 hw₁
  obtain ⟨c₃, w₃, hw₃, rfl⟩ := Submodule.mem_span_insert.1 hw₂
  obtain ⟨c₄, w₄, hw₄, rfl⟩ := Submodule.mem_span_insert.1 hw₃
  obtain ⟨c₅, rfl⟩ := Submodule.mem_span_singleton.1 hw₄
  exact ⟨c₁, c₂, c₃, c₄, c₅, by simp only [Subfield.smul_def, smul_eq_mul]; ring⟩

/-- Complex conjugation as a `ℚ`-algebra map. -/
noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

/-- Conjugation maps `Q̄` to itself. -/
theorem conj_mem_Qbar {a : ℂ} (ha : a ∈ Qbar) : conj a ∈ Qbar := by
  obtain ⟨p, hp0, hp⟩ := mem_Qbar_iff.1 ha
  refine mem_Qbar_iff.2 ⟨p, hp0, ?_⟩
  rw [show (conj a : ℂ) = cjQ a from rfl, Polynomial.aeval_algHom_apply, hp, map_zero]

end R18_C4

open DiazModulus R18_C4 in
theorem solution
    (v : ℂ) (hv : v ∉ Qbar) (hv1 : v * conj v = 1)
    (e β ζ : ℂ) (he : e ∈ Qbar) (hβ : β ∈ Qbar) (hζ : ζ ∈ Qbar) (hβ0 : β ≠ 0)
    (hconj : ∀ w ∈ Submodule.span Qbar ({1, v, conj v, conj v ^ 2 + e * v ^ 2, β * conj v ^ 3 + ζ * v ^ 2 + e * v ^ 3} : Set ℂ),
      conj w ∈ Submodule.span Qbar ({1, v, conj v, conj v ^ 2 + e * v ^ 2, β * conj v ^ 3 + ζ * v ^ 2 + e * v ^ 3} : Set ℂ)) :
    e * conj e = 1 ∧ β * conj β = 1 ∧ ζ = -(β * e ^ 2 * conj ζ) := by
  have h0 := coeffs (hconj _ (Submodule.subset_span (by simp)) :
    conj (conj v ^ 2 + e * v ^ 2) ∈ _)
  have h1 := coeffs (hconj _ (Submodule.subset_span (by simp)) :
    conj (β * conj v ^ 3 + ζ * v ^ 2 + e * v ^ 3) ∈ _)
  obtain ⟨c₁, c₂, c₃, c₄, c₅, h0⟩ := h0
  obtain ⟨d₁, d₂, d₃, d₄, d₅, h1⟩ := h1
  simp only [map_add, map_mul, map_pow, conj_conj] at h0 h1
  obtain ⟨E, rfl⟩ : ∃ E : ↥Qbar, (E : ℂ) = e := ⟨⟨e, he⟩, rfl⟩
  obtain ⟨B, rfl⟩ : ∃ B : ↥Qbar, (B : ℂ) = β := ⟨⟨β, hβ⟩, rfl⟩
  obtain ⟨Z, rfl⟩ : ∃ Z : ↥Qbar, (Z : ℂ) = ζ := ⟨⟨ζ, hζ⟩, rfl⟩
  obtain ⟨CE, hCE⟩ : ∃ CE : ↥Qbar, (CE : ℂ) = conj (E : ℂ) := ⟨⟨_, conj_mem_Qbar E.2⟩, rfl⟩
  obtain ⟨CB, hCB⟩ : ∃ CB : ↥Qbar, (CB : ℂ) = conj (B : ℂ) := ⟨⟨_, conj_mem_Qbar B.2⟩, rfl⟩
  obtain ⟨CZ, hCZ⟩ : ∃ CZ : ↥Qbar, (CZ : ℂ) = conj (Z : ℂ) := ⟨⟨_, conj_mem_Qbar Z.2⟩, rfl⟩
  rw [← hCE] at h0 h1
  rw [← hCB, ← hCZ] at h1
  rw [← hCE, ← hCB, ← hCZ]
  have hB0 : B ≠ 0 := fun h => hβ0 (by rw [h]; rfl)
  set w := conj v
  -- the first relation, times `v³`
  obtain ⟨a₀, a₁, -, -, -, a₅, -⟩ := seven_terms hv (a₀ := c₅ * B) (a₁ := c₄ - CE) (a₂ := c₃)
    (a₃ := c₁) (a₄ := c₂) (a₅ := c₄ * E + c₅ * Z - 1) (a₆ := c₅ * E) (by
      push_cast
      linear_combination (-(v ^ 3)) * h0 + (-(B : ℂ) * c₅ * v ^ 2 * w ^ 2 - B * c₅ * v * w -
        B * c₅ + CE * v ^ 2 * w + CE * v - c₃ * v ^ 2 - c₄ * v ^ 2 * w - c₄ * v) * hv1)
  -- the second relation, times `v³`
  obtain ⟨b₀, b₁, -, -, -, b₅, b₆⟩ := seven_terms hv (a₀ := d₅ * B - CE) (a₁ := d₄ - CZ)
    (a₂ := d₃) (a₃ := d₁) (a₄ := d₂) (a₅ := d₄ * E + d₅ * Z) (a₆ := d₅ * E - CB) (by
      push_cast
      linear_combination (-(v ^ 3)) * h1 + (-(B : ℂ) * d₅ * v ^ 2 * w ^ 2 - B * d₅ * v * w -
        B * d₅ + CE * v ^ 2 * w ^ 2 + CE * v * w + CE + CZ * v ^ 2 * w + CZ * v - d₃ * v ^ 2 -
        d₄ * v ^ 2 * w - d₄ * v) * hv1)
  have hc₅ : c₅ = 0 := (mul_eq_zero.1 a₀).resolve_right hB0
  have hEE : E * CE = 1 := by linear_combination a₅ - E * a₁ - Z * hc₅
  have hBB : B * CB = 1 := by linear_combination (-B) * b₆ + E * b₀ + hEE
  have hZ : Z = -(B * E ^ 2 * CZ) := by
    linear_combination B * E * b₅ - Z * E * b₀ - B * E ^ 2 * b₁ - Z * hEE
  exact ⟨by exact_mod_cast hEE, by exact_mod_cast hBB, by exact_mod_cast hZ⟩
