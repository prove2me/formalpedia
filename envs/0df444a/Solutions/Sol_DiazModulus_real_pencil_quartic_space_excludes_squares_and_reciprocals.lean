-- Prove2me | solution 1 for DiazModulus.real_pencil_quartic_space_excludes_squares_and_reciprocals
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:10:00.592023+00:00
-- url     : https://prove2.me/submissions/6ea49a7e-3c32-4d2f-9cbb-497818c1580c

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The real-pencil quartic space excludes squares and reciprocals

Let `u ∉ Q̄`, `s ∈ Q̄` real with `s² = u ū`, `F = u²/s² + s²/u²`, `G = F/(s + u)` and
`W = span_Q̄ {1, u, ū, F, G}`. Then `ū = s²/u`, `F s² u² = u⁴ + s⁴` and `G (s + u) = F`, with
`s ≠ 0` and `s + u ≠ 0` (else `u = −s ∈ Q̄`).

For `w = c₁ + c₂u + c₃ū + c₄F + c₅G` the product `s²u²(s + u) w` is the polynomial
`Σ aᵢ uⁱ` of degree `5` with `a₀ = c₄s⁵ + c₅s⁴`, `a₁ = c₃s⁵ + c₄s⁴`, `a₂ = c₁s³ + c₃s⁴`,
`a₃ = c₁s² + c₂s³`, `a₄ = c₂s² + c₄s + c₅`, `a₅ = c₄` (`expand`). Since `u` is transcendental
over `Q̄`, an identity `Σ aᵢ uⁱ = Σ tᵢ uⁱ` gives `aᵢ = tᵢ` for every `i` (`core`).
* Freeness (`w = 0`, `t = 0`): successively `c₄, c₅, c₂, c₁, c₃` vanish.
* `w = u²` (`t₄ = s³, t₅ = s²`), `w = ū²` (`t₀ = s⁷, t₁ = s⁶`) and `w = (u + s)⁻¹` (`t₂ = s²`):
  one fixed combination of the six equations, weights `(−1, −s, s², −s³, s⁴, s⁵)`, leaves
  `2s⁷ = 0`, resp. `s⁴ = 0`, impossible.
* `w = (u − b)⁻¹`, `b ≠ −s`: `(u − b) Σ aᵢ uⁱ = s²u²(s + u)` is a polynomial identity over `Q̄`;
  evaluating it at `b` gives `s²b²(s + b) = 0`, impossible.
-/

namespace R11_quarticExcl

open DiazModulus Polynomial

/-- Outside `Q̄`, no non-zero polynomial over `Q̄` vanishes. -/
theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) :
    P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

/-- A polynomial relation of degree `5` over `Q̄` at `u ∉ Q̄` is trivial. -/
theorem six_terms {u : ℂ} (hu : u ∉ Qbar) {a₀ a₁ a₂ a₃ a₄ a₅ : ↥Qbar}
    (h : (a₀ : ℂ) + a₁ * u + a₂ * u ^ 2 + a₃ * u ^ 3 + a₄ * u ^ 4 + a₅ * u ^ 5 = 0) :
    a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 ∧ a₄ = 0 ∧ a₅ = 0 := by
  have hP := aeval_eq_zero hu (P := C a₀ + C a₁ * X + C a₂ * X ^ 2 + C a₃ * X ^ 3 +
    C a₄ * X ^ 4 + C a₅ * X ^ 5)
    (by simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, am]; exact h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 0) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 1) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 2) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 3) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 4) hP
  · simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (coeff · 5) hP

/-- `(u − β) Σ aᵢ uⁱ = σ²u²(σ + u)` forces `σ²β²(σ + β) = 0`: evaluate at `β`. -/
theorem root_eval {u L : ℂ} (hu : u ∉ Qbar) {σ β a₀ a₁ a₂ a₃ a₄ a₅ : ↥Qbar}
    (hE : L = (a₀ : ℂ) + a₁ * u + a₂ * u ^ 2 + a₃ * u ^ 3 + a₄ * u ^ 4 + a₅ * u ^ 5)
    (hL : (u - β) * L = (σ : ℂ) ^ 2 * u ^ 2 * (σ + u)) : σ ^ 2 * β ^ 2 * (σ + β) = 0 := by
  have hP := aeval_eq_zero hu (P := (X - C β) * (C a₀ + C a₁ * X + C a₂ * X ^ 2 + C a₃ * X ^ 3 +
    C a₄ * X ^ 4 + C a₅ * X ^ 5) - C σ ^ 2 * X ^ 2 * (C σ + X))
    (by
      simp only [map_sub, map_add, map_mul, map_pow, aeval_C, aeval_X, am]
      linear_combination hL - (u - β) * hE)
  have := congrArg (eval β) hP
  simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X, sub_self, zero_mul,
    zero_sub, eval_zero, neg_eq_zero] at this
  exact this

theorem coeffs {u z zc t w : ℂ} (hw : w ∈ Submodule.span Qbar ({1, u, t, z, zc} : Set ℂ)) :
    ∃ c₁ c₂ c₃ c₄ c₅ : ↥Qbar, w = (c₁ : ℂ) + c₂ * u + c₃ * t + c₄ * z + c₅ * zc := by
  obtain ⟨c₁, w₁, hw₁, rfl⟩ := Submodule.mem_span_insert.1 hw
  obtain ⟨c₂, w₂, hw₂, rfl⟩ := Submodule.mem_span_insert.1 hw₁
  obtain ⟨c₃, w₃, hw₃, rfl⟩ := Submodule.mem_span_insert.1 hw₂
  obtain ⟨c₄, w₄, hw₄, rfl⟩ := Submodule.mem_span_insert.1 hw₃
  obtain ⟨c₅, rfl⟩ := Submodule.mem_span_singleton.1 hw₄
  exact ⟨c₁, c₂, c₃, c₄, c₅, by simp only [Subfield.smul_def, smul_eq_mul]; ring⟩

/-- Clearing denominators: `σ²u²(σ + u) w` as a polynomial of degree `5` in `u`. -/
theorem expand {u cu F G w : ℂ} {σ c₁ c₂ c₃ c₄ c₅ : ↥Qbar}
    (hcu : cu * u = σ * σ) (hF : F * (σ * σ * u ^ 2) = u ^ 4 + (σ * σ) ^ 2)
    (hG : G * (σ + u) = F) (h : w = c₁ + c₂ * u + c₃ * cu + c₄ * F + c₅ * G) :
    (σ : ℂ) ^ 2 * u ^ 2 * (σ + u) * w =
      ((c₄ * σ ^ 5 + c₅ * σ ^ 4 : ↥Qbar) : ℂ) + ((c₃ * σ ^ 5 + c₄ * σ ^ 4 : ↥Qbar) : ℂ) * u +
      ((c₁ * σ ^ 3 + c₃ * σ ^ 4 : ↥Qbar) : ℂ) * u ^ 2 +
      ((c₁ * σ ^ 2 + c₂ * σ ^ 3 : ↥Qbar) : ℂ) * u ^ 3 +
      ((c₂ * σ ^ 2 + c₄ * σ + c₅ : ↥Qbar) : ℂ) * u ^ 4 + (c₄ : ℂ) * u ^ 5 := by
  push_cast
  linear_combination (σ : ℂ) ^ 2 * u ^ 2 * (σ + u) * h + (c₃ : ℂ) * σ ^ 2 * u * (σ + u) * hcu +
    (c₄ : ℂ) * (σ + u) * hF + (c₅ : ℂ) * σ ^ 2 * u ^ 2 * hG + (c₅ : ℂ) * hF

/-- Comparing coefficients of `σ²u²(σ + u) w = Σ tᵢ uⁱ`. -/
theorem core {u cu F G w : ℂ} (hu : u ∉ Qbar) {σ c₁ c₂ c₃ c₄ c₅ t₀ t₁ t₂ t₃ t₄ t₅ : ↥Qbar}
    (hcu : cu * u = σ * σ) (hF : F * (σ * σ * u ^ 2) = u ^ 4 + (σ * σ) ^ 2)
    (hG : G * (σ + u) = F) (h : w = c₁ + c₂ * u + c₃ * cu + c₄ * F + c₅ * G)
    (ht : (σ : ℂ) ^ 2 * u ^ 2 * (σ + u) * w =
      (t₀ : ℂ) + t₁ * u + t₂ * u ^ 2 + t₃ * u ^ 3 + t₄ * u ^ 4 + t₅ * u ^ 5) :
    c₄ * σ ^ 5 + c₅ * σ ^ 4 = t₀ ∧ c₃ * σ ^ 5 + c₄ * σ ^ 4 = t₁ ∧ c₁ * σ ^ 3 + c₃ * σ ^ 4 = t₂ ∧
      c₁ * σ ^ 2 + c₂ * σ ^ 3 = t₃ ∧ c₂ * σ ^ 2 + c₄ * σ + c₅ = t₄ ∧ c₄ = t₅ := by
  have E := expand hcu hF hG h
  obtain ⟨e₀, e₁, e₂, e₃, e₄, e₅⟩ := six_terms hu (a₀ := c₄ * σ ^ 5 + c₅ * σ ^ 4 - t₀)
    (a₁ := c₃ * σ ^ 5 + c₄ * σ ^ 4 - t₁) (a₂ := c₁ * σ ^ 3 + c₃ * σ ^ 4 - t₂)
    (a₃ := c₁ * σ ^ 2 + c₂ * σ ^ 3 - t₃) (a₄ := c₂ * σ ^ 2 + c₄ * σ + c₅ - t₄) (a₅ := c₄ - t₅)
    (by push_cast at E ⊢; linear_combination ht - E)
  exact ⟨sub_eq_zero.1 e₀, sub_eq_zero.1 e₁, sub_eq_zero.1 e₂, sub_eq_zero.1 e₃,
    sub_eq_zero.1 e₄, sub_eq_zero.1 e₅⟩

/-- The statement for abstract `ū, F, G` satisfying the three defining identities. -/
theorem main {u cu F G : ℂ} (hu : u ∉ Qbar) {σ : ↥Qbar} (hσ : σ ≠ 0)
    (hcu : cu * u = σ * σ) (hF : F * (σ * σ * u ^ 2) = u ^ 4 + (σ * σ) ^ 2)
    (hG : G * (σ + u) = F) :
    LinearIndependent (↥Qbar) ![1, u, cu, F, G] ∧
      u ^ 2 ∉ Submodule.span Qbar ({1, u, cu, F, G} : Set ℂ) ∧
      cu ^ 2 ∉ Submodule.span Qbar ({1, u, cu, F, G} : Set ℂ) ∧
      ∀ b ∈ Qbar, b ≠ 0 → (u - b)⁻¹ ∉ Submodule.span Qbar ({1, u, cu, F, G} : Set ℂ) := by
  have h2 : (2 : ↥Qbar) ≠ 0 := two_ne_zero
  refine ⟨?_, fun hw => ?_, fun hw => ?_, fun b hb hb0 hw => ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    simp [Fin.sum_univ_five, Subfield.smul_def] at hg
    obtain ⟨e₀, e₁, -, e₃, e₄, e₅⟩ := core hu (w := 0) (c₁ := g 0) (c₂ := g 1) (c₃ := g 2)
      (c₄ := g 3) (c₅ := g 4) (t₀ := 0) (t₁ := 0) (t₂ := 0) (t₃ := 0)
      (t₄ := 0) (t₅ := 0) hcu hF hG (by linear_combination -hg) (by simp)
    have h5 : g 4 * σ ^ 4 = 0 := by linear_combination e₀ - σ ^ 5 * e₅
    have h5' := (mul_eq_zero.1 h5).resolve_right (pow_ne_zero 4 hσ)
    have h2' : g 1 * σ ^ 2 = 0 := by linear_combination e₄ - σ * e₅ - h5'
    have h2'' := (mul_eq_zero.1 h2').resolve_right (pow_ne_zero 2 hσ)
    have h1 : g 0 * σ ^ 2 = 0 := by linear_combination e₃ - σ ^ 3 * h2''
    have h1' := (mul_eq_zero.1 h1).resolve_right (pow_ne_zero 2 hσ)
    have h3 : g 2 * σ ^ 5 = 0 := by linear_combination e₁ - σ ^ 4 * e₅
    have h3' := (mul_eq_zero.1 h3).resolve_right (pow_ne_zero 5 hσ)
    intro i
    fin_cases i
    · exact h1'
    · exact h2''
    · exact h3'
    · exact e₅
    · exact h5'
  · obtain ⟨c₁, c₂, c₃, c₄, c₅, h⟩ := coeffs hw
    obtain ⟨e₀, e₁, e₂, e₃, e₄, e₅⟩ := core hu (t₀ := 0) (t₁ := 0) (t₂ := 0) (t₃ := 0)
      (t₄ := σ ^ 3) (t₅ := σ ^ 2) hcu hF hG h (by push_cast; ring)
    have : 2 * σ ^ 7 = 0 := by
      linear_combination e₀ + σ * e₁ - σ ^ 2 * e₂ + σ ^ 3 * e₃ - σ ^ 4 * e₄ - σ ^ 5 * e₅
    exact pow_ne_zero 7 hσ ((mul_eq_zero.1 this).resolve_left h2)
  · obtain ⟨c₁, c₂, c₃, c₄, c₅, h⟩ := coeffs hw
    obtain ⟨e₀, e₁, e₂, e₃, e₄, e₅⟩ := core hu (t₀ := σ ^ 7) (t₁ := σ ^ 6) (t₂ := 0) (t₃ := 0)
      (t₄ := 0) (t₅ := 0) hcu hF hG h
      (by push_cast; linear_combination (σ : ℂ) ^ 2 * (σ + u) * (cu * u + σ * σ) * hcu)
    have : 2 * σ ^ 7 = 0 := by
      linear_combination -e₀ - σ * e₁ + σ ^ 2 * e₂ - σ ^ 3 * e₃ + σ ^ 4 * e₄ + σ ^ 5 * e₅
    exact pow_ne_zero 7 hσ ((mul_eq_zero.1 this).resolve_left h2)
  · obtain ⟨c₁, c₂, c₃, c₄, c₅, h⟩ := coeffs hw
    obtain ⟨β, rfl⟩ : ∃ β : ↥Qbar, (β : ℂ) = b := ⟨⟨b, hb⟩, rfl⟩
    have hβ0 : β ≠ 0 := by rintro rfl; exact hb0 rfl
    have hub : (u - β) * (u - β)⁻¹ = 1 :=
      mul_inv_cancel₀ (sub_ne_zero.2 fun e => hu (by rw [e]; exact β.2))
    by_cases hβσ : β = -σ
    · rw [hβσ] at hub h
      obtain ⟨e₀, e₁, e₂, e₃, e₄, e₅⟩ := core hu (t₀ := 0) (t₁ := 0) (t₂ := σ ^ 2) (t₃ := 0)
        (t₄ := 0) (t₅ := 0) hcu hF hG h
        (by push_cast at hub ⊢; linear_combination (σ : ℂ) ^ 2 * u ^ 2 * hub)
      have : σ ^ 4 = 0 := by
        linear_combination e₀ + σ * e₁ - σ ^ 2 * e₂ + σ ^ 3 * e₃ - σ ^ 4 * e₄ - σ ^ 5 * e₅
      exact pow_ne_zero 4 hσ this
    · have := root_eval hu (σ := σ) (β := β) (expand hcu hF hG h)
        (by linear_combination (σ : ℂ) ^ 2 * u ^ 2 * (σ + u) * hub)
      simp only [mul_eq_zero, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        hσ, hβ0, false_or] at this
      exact hβσ (by linear_combination this)

end R11_quarticExcl

open DiazModulus R11_quarticExcl in
theorem solution
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u) :
    LinearIndependent (↥Qbar) ![1, u, conj u, (u ^ 2 / (s * s) + s * s / u ^ 2), (u ^ 2 / (s * s) + s * s / u ^ 2) / (s + 1 * u)] ∧
      u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u, (u ^ 2 / (s * s) + s * s / u ^ 2), (u ^ 2 / (s * s) + s * s / u ^ 2) / (s + 1 * u)} : Set ℂ) ∧
      conj u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u, (u ^ 2 / (s * s) + s * s / u ^ 2), (u ^ 2 / (s * s) + s * s / u ^ 2) / (s + 1 * u)} : Set ℂ) ∧
      ∀ b ∈ Qbar, b ≠ 0 → (u - b)⁻¹ ∉ Submodule.span Qbar ({1, u, conj u, (u ^ 2 / (s * s) + s * s / u ^ 2), (u ^ 2 / (s * s) + s * s / u ^ 2) / (s + 1 * u)} : Set ℂ) := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Subfield.zero_mem _)
  have hcu0 : conj u ≠ 0 := (map_ne_zero _).2 hu0
  obtain ⟨σ, rfl⟩ : ∃ σ : ↥Qbar, (σ : ℂ) = s := ⟨⟨s, hs⟩, rfl⟩
  have hs0 : (σ : ℂ) ≠ 0 := by
    intro h
    rw [h] at hss
    exact mul_ne_zero hu0 hcu0 (by rw [← hss]; ring)
  have hσ : σ ≠ 0 := by rintro rfl; exact hs0 rfl
  have hD : (σ : ℂ) + 1 * u ≠ 0 := by
    intro h
    exact hu (by rw [show u = -σ by linear_combination h]; exact neg_mem σ.2)
  have hcu : conj u * u = σ * σ := by rw [hss]; ring
  have hF : (u ^ 2 / (σ * σ) + σ * σ / u ^ 2) * (σ * σ * u ^ 2) = u ^ 4 + (σ * σ) ^ 2 := by
    field_simp
  have hG : (u ^ 2 / (σ * σ) + σ * σ / u ^ 2) / (σ + 1 * u) * (σ + u) =
      u ^ 2 / (σ * σ) + σ * σ / u ^ 2 := by
    simpa only [one_mul] using div_mul_cancel₀ (u ^ 2 / (σ * σ) + σ * σ / u ^ 2) hD
  exact main hu hσ hcu hF hG
