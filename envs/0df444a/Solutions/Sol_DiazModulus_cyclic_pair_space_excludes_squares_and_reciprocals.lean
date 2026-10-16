-- Prove2me | solution 1 for DiazModulus.cyclic_pair_space_excludes_squares_and_reciprocals
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-15T12:02:13.034859+00:00
-- url     : https://prove2.me/submissions/9bf571b8-b674-4be5-88fa-a39d4c68e6ba

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The cyclic pair space excludes squares and reciprocals

Let `u ∉ Q̄`, `s ∈ Q̄` real with `s² = u ū`, `G₁ = s/(u − s) + 2s/(u + s)`,
`G₂ = s²/(u − s)² + s/(u − s) − 2s²/(u + s)² + 2s/(u + s)` and `W = span_Q̄ {1, u, ū, G₁, G₂}`.
Then `u ≠ ±s`, `ū u = s²`, `G₁ (u² − s²) = s(3u − s)` and `G₂ (u² − s²)² = s u (3u² − 2su + 3s²)`.

For `w = c₁ + c₂u + c₃ū + c₄G₁ + c₅G₂` the product `u(u² − s²)² w` is a polynomial `Σ pᵢ uⁱ` of
degree `6` over `Q̄`, with `p₀ = c₃s⁶`, `p₁ = (c₁ + c₄)s⁴`, `p₅ = c₁`, `p₆ = c₂` (`expand`). As `u`
is transcendental, `(m₀ + m₁u) Σ pᵢ uⁱ = Σ tᵢ uⁱ` gives eight coefficient equations (`mul_core`).
* Freeness (`w = 0`): `c₂ = c₁ = 0`, then `c₃s⁶ = 0`, `c₄s⁴ = 0` and `3c₅s = 0`.
* `u²`: the target `u³(u² − s²)²` has a `u⁷` term, the left side has none.
* `ū² = s⁴/u²` (multiply by `u`): the target `s⁴(u² − s²)²` has constant term `s⁸`, the left none.
* `(u − e)⁻¹` (multiply by `u − e`, target `u(u² − s²)²`): the equations summed against `eᵏ`
  evaluate at `e`, so `e(e² − s²)² = 0` and `e = ±s`; at the poles the residues of `W` at `s` and
  `−s` are tied together, and explicit combinations give `8s⁵ = 0`, resp. `4s⁵ = 0`.
-/

namespace R15_cyclicExcl

open DiazModulus Polynomial

/-- Outside `Q̄`, no non-zero polynomial over `Q̄` vanishes. -/
theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) :
    P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem c2 : ((2 : ↥Qbar) : ℂ) = 2 := rfl
theorem c3 : ((3 : ↥Qbar) : ℂ) = 3 := rfl

/-- A polynomial relation of degree `7` over `Q̄` at `u ∉ Q̄` is trivial. -/
theorem eight_terms {u : ℂ} (hu : u ∉ Qbar) {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ↥Qbar}
    (h : (a₀ : ℂ) + a₁ * u + a₂ * u ^ 2 + a₃ * u ^ 3 + a₄ * u ^ 4 + a₅ * u ^ 5 +
      a₆ * u ^ 6 + a₇ * u ^ 7 = 0) :
    a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 ∧ a₄ = 0 ∧ a₅ = 0 ∧ a₆ = 0 ∧ a₇ = 0 := by
  have hP := aeval_eq_zero hu (P := C a₀ + C a₁ * X + C a₂ * X ^ 2 + C a₃ * X ^ 3 +
    C a₄ * X ^ 4 + C a₅ * X ^ 5 + C a₆ * X ^ 6 + C a₇ * X ^ 7)
    (by simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, am]; exact h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 0) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 1) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 2) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 3) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 4) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 5) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 6) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 7) hP

/-- `(m₀ + m₁u) Σ pᵢ uⁱ = Σ tᵢ uⁱ` at the transcendental `u`: compare coefficients. -/
theorem mul_core {u L : ℂ} (hu : u ∉ Qbar)
    {p₀ p₁ p₂ p₃ p₄ p₅ p₆ m₀ m₁ t₀ t₁ t₂ t₃ t₄ t₅ t₆ t₇ : ↥Qbar}
    (hL : L = (p₀ : ℂ) + p₁ * u + p₂ * u ^ 2 + p₃ * u ^ 3 + p₄ * u ^ 4 + p₅ * u ^ 5 + p₆ * u ^ 6)
    (ht : ((m₀ : ℂ) + m₁ * u) * L = (t₀ : ℂ) + t₁ * u + t₂ * u ^ 2 + t₃ * u ^ 3 + t₄ * u ^ 4 +
      t₅ * u ^ 5 + t₆ * u ^ 6 + t₇ * u ^ 7) :
    m₀ * p₀ = t₀ ∧ m₀ * p₁ + m₁ * p₀ = t₁ ∧ m₀ * p₂ + m₁ * p₁ = t₂ ∧ m₀ * p₃ + m₁ * p₂ = t₃ ∧
      m₀ * p₄ + m₁ * p₃ = t₄ ∧ m₀ * p₅ + m₁ * p₄ = t₅ ∧ m₀ * p₆ + m₁ * p₅ = t₆ ∧
      m₁ * p₆ = t₇ := by
  obtain ⟨e₀, e₁, e₂, e₃, e₄, e₅, e₆, e₇⟩ := eight_terms hu (a₀ := m₀ * p₀ - t₀)
    (a₁ := m₀ * p₁ + m₁ * p₀ - t₁) (a₂ := m₀ * p₂ + m₁ * p₁ - t₂) (a₃ := m₀ * p₃ + m₁ * p₂ - t₃)
    (a₄ := m₀ * p₄ + m₁ * p₃ - t₄) (a₅ := m₀ * p₅ + m₁ * p₄ - t₅) (a₆ := m₀ * p₆ + m₁ * p₅ - t₆)
    (a₇ := m₁ * p₆ - t₇) (by push_cast; linear_combination ht - ((m₀ : ℂ) + m₁ * u) * hL)
  exact ⟨sub_eq_zero.1 e₀, sub_eq_zero.1 e₁, sub_eq_zero.1 e₂, sub_eq_zero.1 e₃,
    sub_eq_zero.1 e₄, sub_eq_zero.1 e₅, sub_eq_zero.1 e₆, sub_eq_zero.1 e₇⟩

theorem coeffs {u z zc t w : ℂ} (hw : w ∈ Submodule.span Qbar ({1, u, t, z, zc} : Set ℂ)) :
    ∃ c₁ c₂ c₃ c₄ c₅ : ↥Qbar, w = (c₁ : ℂ) + c₂ * u + c₃ * t + c₄ * z + c₅ * zc := by
  obtain ⟨c₁, w₁, hw₁, rfl⟩ := Submodule.mem_span_insert.1 hw
  obtain ⟨c₂, w₂, hw₂, rfl⟩ := Submodule.mem_span_insert.1 hw₁
  obtain ⟨c₃, w₃, hw₃, rfl⟩ := Submodule.mem_span_insert.1 hw₂
  obtain ⟨c₄, w₄, hw₄, rfl⟩ := Submodule.mem_span_insert.1 hw₃
  obtain ⟨c₅, rfl⟩ := Submodule.mem_span_singleton.1 hw₄
  exact ⟨c₁, c₂, c₃, c₄, c₅, by simp only [Subfield.smul_def, smul_eq_mul]; ring⟩

/-- Clearing denominators: `u(u² − σ²)² w` as a polynomial of degree `6` in `u`. -/
theorem expand {u cu G₁ G₂ w : ℂ} {σ c₁ c₂ c₃ c₄ c₅ : ↥Qbar}
    (hcu : cu * u = σ * σ) (hG₁ : G₁ * (u ^ 2 - σ ^ 2) = σ * (3 * u - σ))
    (hG₂ : G₂ * (u ^ 2 - σ ^ 2) ^ 2 = σ * u * (3 * u ^ 2 - 2 * σ * u + 3 * σ ^ 2))
    (h : w = c₁ + c₂ * u + c₃ * cu + c₄ * G₁ + c₅ * G₂) :
    u * (u ^ 2 - σ ^ 2) ^ 2 * w =
      ((c₃ * σ ^ 6 : ↥Qbar) : ℂ) + (((c₁ + c₄) * σ ^ 4 : ↥Qbar) : ℂ) * u +
      (((c₂ - 2 * c₃) * σ ^ 4 + 3 * (c₅ - c₄) * σ ^ 3 : ↥Qbar) : ℂ) * u ^ 2 +
      ((-(2 * c₁ + c₄ + 2 * c₅) * σ ^ 2 : ↥Qbar) : ℂ) * u ^ 3 +
      (((c₃ - 2 * c₂) * σ ^ 2 + 3 * (c₄ + c₅) * σ : ↥Qbar) : ℂ) * u ^ 4 +
      (c₁ : ℂ) * u ^ 5 + (c₂ : ℂ) * u ^ 6 := by
  push_cast [c2, c3]
  linear_combination u * (u ^ 2 - (σ : ℂ) ^ 2) ^ 2 * h + (c₃ : ℂ) * (u ^ 2 - σ ^ 2) ^ 2 * hcu +
    (c₄ : ℂ) * u * (u ^ 2 - σ ^ 2) * hG₁ + (c₅ : ℂ) * u * hG₂

/-- The statement for abstract `ū, G₁, G₂` satisfying the three defining identities. -/
theorem main {u cu G₁ G₂ : ℂ} (hu : u ∉ Qbar) {σ : ↥Qbar} (hσ : σ ≠ 0)
    (hcu : cu * u = σ * σ) (hG₁ : G₁ * (u ^ 2 - σ ^ 2) = σ * (3 * u - σ))
    (hG₂ : G₂ * (u ^ 2 - σ ^ 2) ^ 2 = σ * u * (3 * u ^ 2 - 2 * σ * u + 3 * σ ^ 2)) :
    LinearIndependent (↥Qbar) ![1, u, cu, G₁, G₂] ∧
      u ^ 2 ∉ Submodule.span Qbar ({1, u, cu, G₁, G₂} : Set ℂ) ∧
      cu ^ 2 ∉ Submodule.span Qbar ({1, u, cu, G₁, G₂} : Set ℂ) ∧
      ∀ e ∈ Qbar, e ≠ 0 → (u - e)⁻¹ ∉ Submodule.span Qbar ({1, u, cu, G₁, G₂} : Set ℂ) := by
  refine ⟨?_, fun hw => ?_, fun hw => ?_, fun b hb hb0 hw => ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    simp [Fin.sum_univ_five, Subfield.smul_def] at hg
    obtain ⟨e₀, e₁, -, -, e₄, e₅, e₆, -⟩ := mul_core hu (m₀ := 1) (m₁ := 0) (t₀ := 0) (t₁ := 0)
      (t₂ := 0) (t₃ := 0) (t₄ := 0) (t₅ := 0) (t₆ := 0) (t₇ := 0)
      (expand (w := 0) (c₁ := g 0) (c₂ := g 1) (c₃ := g 2) (c₄ := g 3) (c₅ := g 4) hcu hG₁ hG₂
        (by linear_combination -hg)) (by simp)
    have h2 : g 1 = 0 := by linear_combination e₆
    have h1 : g 0 = 0 := by linear_combination e₅
    have h3 := (mul_eq_zero.1 (show g 2 * σ ^ 6 = 0 by linear_combination e₀)).resolve_right
      (pow_ne_zero 6 hσ)
    have h4 := (mul_eq_zero.1 (show g 3 * σ ^ 4 = 0 by linear_combination e₁ - σ ^ 4 * h1)).resolve_right
      (pow_ne_zero 4 hσ)
    have h5 := (mul_eq_zero.1 (show g 4 * (3 * σ) = 0 by
      linear_combination e₄ - σ ^ 2 * h3 + 2 * σ ^ 2 * h2 - 3 * σ * h4)).resolve_right
      (mul_ne_zero (by norm_num) hσ)
    intro i
    fin_cases i
    exacts [h1, h2, h3, h4, h5]
  · obtain ⟨c₁, c₂, c₃, c₄, c₅, h⟩ := coeffs hw
    obtain ⟨-, -, -, -, -, -, -, e₇⟩ := mul_core hu (m₀ := 1) (m₁ := 0) (t₀ := 0) (t₁ := 0)
      (t₂ := 0) (t₃ := σ ^ 4) (t₄ := 0) (t₅ := -2 * σ ^ 2) (t₆ := 0) (t₇ := 1)
      (expand hcu hG₁ hG₂ h) (by push_cast [c2]; ring)
    simp at e₇
  · obtain ⟨c₁, c₂, c₃, c₄, c₅, h⟩ := coeffs hw
    obtain ⟨e₀, -⟩ := mul_core hu (m₀ := 0) (m₁ := 1) (t₀ := σ ^ 8) (t₁ := 0)
      (t₂ := -2 * σ ^ 6) (t₃ := 0) (t₄ := σ ^ 4) (t₅ := 0) (t₆ := 0) (t₇ := 0)
      (expand hcu hG₁ hG₂ h)
      (by push_cast [c2]; linear_combination (cu * u + σ * σ) * (u ^ 2 - (σ : ℂ) ^ 2) ^ 2 * hcu)
    exact pow_ne_zero 8 hσ (by linear_combination -e₀)
  · obtain ⟨c₁, c₂, c₃, c₄, c₅, h⟩ := coeffs hw
    obtain ⟨β, rfl⟩ : ∃ β : ↥Qbar, (β : ℂ) = b := ⟨⟨b, hb⟩, rfl⟩
    have hβ0 : β ≠ 0 := by rintro rfl; exact hb0 rfl
    have hub : (u - β) * (u - β)⁻¹ = 1 :=
      mul_inv_cancel₀ (sub_ne_zero.2 fun e => hu (by rw [e]; exact β.2))
    obtain ⟨e₀, e₁, e₂, e₃, e₄, e₅, e₆, e₇⟩ := mul_core hu (m₀ := -β) (m₁ := 1) (t₀ := 0)
      (t₁ := σ ^ 4) (t₂ := 0) (t₃ := -2 * σ ^ 2) (t₄ := 0) (t₅ := 1) (t₆ := 0) (t₇ := 0)
      (expand hcu hG₁ hG₂ h)
      (by push_cast [c2]; linear_combination u * (u ^ 2 - (σ : ℂ) ^ 2) ^ 2 * hub)
    -- evaluation at `β`
    have hev : β * ((β - σ) * (β + σ)) ^ 2 = 0 := by
      linear_combination -(e₀ + β * e₁ + β ^ 2 * e₂ + β ^ 3 * e₃ + β ^ 4 * e₄ + β ^ 5 * e₅ +
        β ^ 6 * e₆ + β ^ 7 * e₇)
    rcases mul_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1
      ((mul_eq_zero.1 hev).resolve_left hβ0)) with h' | h'
    · rw [sub_eq_zero.1 h'] at e₀ e₁ e₂ e₃ e₄ e₅
      exact mul_ne_zero (by norm_num) (pow_ne_zero 5 hσ) (show (8 : ↥Qbar) * σ ^ 5 = 0 by
        linear_combination -(39 * e₀ + 33 * σ * e₁ + 18 * σ ^ 2 * e₂ + 14 * σ ^ 3 * e₃ +
          5 * σ ^ 4 * e₄ + 3 * σ ^ 5 * e₅))
    · rw [eq_neg_of_add_eq_zero_left h'] at e₀ e₁ e₂ e₃ e₄ e₅
      exact mul_ne_zero (by norm_num) (pow_ne_zero 5 hσ) (show (4 : ↥Qbar) * σ ^ 5 = 0 by
        linear_combination -(-15 * e₀ + 21 * σ * e₁ - 6 * σ ^ 2 * e₂ + 10 * σ ^ 3 * e₃ -
          σ ^ 4 * e₄ + 3 * σ ^ 5 * e₅))

end R15_cyclicExcl

open DiazModulus R15_cyclicExcl in
theorem solution
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u) :
    LinearIndependent (↥Qbar) ![1, u, conj u, (s / (u - s) + 2 * s / (u + s)), (s * s / (u - s) ^ 2 + s / (u - s) - 2 * (s * s) / (u + s) ^ 2 + 2 * s / (u + s))] ∧
      u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u, (s / (u - s) + 2 * s / (u + s)), (s * s / (u - s) ^ 2 + s / (u - s) - 2 * (s * s) / (u + s) ^ 2 + 2 * s / (u + s))} : Set ℂ) ∧
      conj u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u, (s / (u - s) + 2 * s / (u + s)), (s * s / (u - s) ^ 2 + s / (u - s) - 2 * (s * s) / (u + s) ^ 2 + 2 * s / (u + s))} : Set ℂ) ∧
      ∀ e ∈ Qbar, e ≠ 0 → (u - e)⁻¹ ∉ Submodule.span Qbar ({1, u, conj u, (s / (u - s) + 2 * s / (u + s)), (s * s / (u - s) ^ 2 + s / (u - s) - 2 * (s * s) / (u + s) ^ 2 + 2 * s / (u + s))} : Set ℂ) := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Subfield.zero_mem _)
  have hcu0 : conj u ≠ 0 := (map_ne_zero _).2 hu0
  obtain ⟨σ, rfl⟩ : ∃ σ : ↥Qbar, (σ : ℂ) = s := ⟨⟨s, hs⟩, rfl⟩
  have hs0 : (σ : ℂ) ≠ 0 := by
    intro h
    rw [h] at hss
    exact mul_ne_zero hu0 hcu0 (by rw [← hss]; ring)
  have hσ : σ ≠ 0 := by rintro rfl; exact hs0 rfl
  have hm : u - σ ≠ 0 := sub_ne_zero.2 fun e => hu (by rw [e]; exact σ.2)
  have hp : u + σ ≠ 0 := fun e => hu (by rw [eq_neg_of_add_eq_zero_left e]; exact neg_mem σ.2)
  have hcu : conj u * u = σ * σ := by rw [hss]; ring
  have hG₁ : ((σ : ℂ) / (u - σ) + 2 * σ / (u + σ)) * (u ^ 2 - σ ^ 2) = σ * (3 * u - σ) := by
    field_simp
    ring
  have hG₂ : ((σ : ℂ) * σ / (u - σ) ^ 2 + σ / (u - σ) - 2 * (σ * σ) / (u + σ) ^ 2 +
      2 * σ / (u + σ)) * (u ^ 2 - σ ^ 2) ^ 2 = σ * u * (3 * u ^ 2 - 2 * σ * u + 3 * σ ^ 2) := by
    field_simp
    ring
  exact main hu hσ hcu hG₁ hG₂
