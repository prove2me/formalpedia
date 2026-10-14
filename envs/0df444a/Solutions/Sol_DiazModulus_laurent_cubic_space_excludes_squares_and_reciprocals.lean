-- Prove2me | solution 1 for DiazModulus.laurent_cubic_space_excludes_squares_and_reciprocals
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T07:34:16.041116+00:00
-- url     : https://prove2.me/submissions/2ec2288a-2607-4582-b143-62b4ca35fb70

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The Laurent cubic space excludes squares and reciprocals

Let `u ∉ Q̄`, `s ∈ Q̄` real with `s² = u ū`, `F = u³/s³ + u²/s²`, `G = ū³/s³ + ū²/s²` and
`W₁ = span_Q̄ {1, u, ū, F, G}`. Then `u ≠ 0`, `s ≠ 0`, `ū u = s²`, `F s³ = u³ + s u²` and
`G u³ = s³ + s² u` (so in `v = u/s` the space is spanned by `1, v, v⁻¹, v³ + v², v⁻³ + v⁻²`).

For `w = c₁ + c₂u + c₃ū + c₄F + c₅G` the product `s³u³ w` is the polynomial `Σ aᵢ uⁱ` of
degree `6` with `a₀ = c₅s⁶`, `a₁ = c₅s⁵`, `a₂ = c₃s⁵`, `a₃ = c₁s³`, `a₄ = c₂s³`, `a₅ = c₄s`,
`a₆ = c₄` (`expand`). Since `u` is transcendental over `Q̄`, an identity `Σ aᵢ uⁱ = Σ tᵢ uⁱ`
gives `aᵢ = tᵢ` for every `i` (`core`).
* Freeness (`w = 0`, `t = 0`): every `cᵢ` vanishes, as `s ≠ 0`.
* `w = u²` (`t₅ = s³`): the `u⁵` and `u⁶` coefficients are tied, `c₄ s = s³` and `c₄ = 0`.
* `w = ū² = s⁴/u²` (`t₁ = s⁷`): the `u⁰` and `u¹` coefficients are tied, `c₅ s⁶ = 0` and
  `c₅ s⁵ = s⁷`.
* `w = (u − b)⁻¹`: `(u − b) Σ aᵢ uⁱ = s³u³` is a polynomial identity over `Q̄`; evaluating it
  at `b` gives `s³b³ = 0`, impossible.
-/

namespace R14_cubicExcl

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

/-- `(u − β) Σ aᵢ uⁱ = σ³u³` forces `σ³β³ = 0`: evaluate at `β`. -/
theorem root_eval {u L : ℂ} (hu : u ∉ Qbar) {σ β a₀ a₁ a₂ a₃ a₄ a₅ a₆ : ↥Qbar}
    (hE : L = (a₀ : ℂ) + a₁ * u + a₂ * u ^ 2 + a₃ * u ^ 3 + a₄ * u ^ 4 + a₅ * u ^ 5 +
      a₆ * u ^ 6)
    (hL : (u - β) * L = (σ : ℂ) ^ 3 * u ^ 3) : σ ^ 3 * β ^ 3 = 0 := by
  have hP := aeval_eq_zero hu (P := (X - C β) * (C a₀ + C a₁ * X + C a₂ * X ^ 2 + C a₃ * X ^ 3 +
    C a₄ * X ^ 4 + C a₅ * X ^ 5 + C a₆ * X ^ 6) - C σ ^ 3 * X ^ 3)
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

/-- Clearing denominators: `σ³u³ w` as a polynomial of degree `6` in `u`. -/
theorem expand {u cu F G w : ℂ} {σ c₁ c₂ c₃ c₄ c₅ : ↥Qbar}
    (hcu : cu * u = σ * σ) (hF : F * (σ * σ * σ) = u ^ 3 + σ * u ^ 2)
    (hG : G * u ^ 3 = σ ^ 3 + σ ^ 2 * u) (h : w = c₁ + c₂ * u + c₃ * cu + c₄ * F + c₅ * G) :
    (σ : ℂ) ^ 3 * u ^ 3 * w =
      ((c₅ * σ ^ 6 : ↥Qbar) : ℂ) + ((c₅ * σ ^ 5 : ↥Qbar) : ℂ) * u +
      ((c₃ * σ ^ 5 : ↥Qbar) : ℂ) * u ^ 2 + ((c₁ * σ ^ 3 : ↥Qbar) : ℂ) * u ^ 3 +
      ((c₂ * σ ^ 3 : ↥Qbar) : ℂ) * u ^ 4 + ((c₄ * σ : ↥Qbar) : ℂ) * u ^ 5 + (c₄ : ℂ) * u ^ 6 := by
  push_cast
  linear_combination (σ : ℂ) ^ 3 * u ^ 3 * h + (c₃ : ℂ) * σ ^ 3 * u ^ 2 * hcu +
    (c₄ : ℂ) * u ^ 3 * hF + (c₅ : ℂ) * σ ^ 3 * hG

/-- Comparing coefficients of `σ³u³ w = Σ tᵢ uⁱ`. -/
theorem core {u cu F G w : ℂ} (hu : u ∉ Qbar) {σ c₁ c₂ c₃ c₄ c₅ t₀ t₁ t₂ t₃ t₄ t₅ t₆ : ↥Qbar}
    (hcu : cu * u = σ * σ) (hF : F * (σ * σ * σ) = u ^ 3 + σ * u ^ 2)
    (hG : G * u ^ 3 = σ ^ 3 + σ ^ 2 * u) (h : w = c₁ + c₂ * u + c₃ * cu + c₄ * F + c₅ * G)
    (ht : (σ : ℂ) ^ 3 * u ^ 3 * w =
      (t₀ : ℂ) + t₁ * u + t₂ * u ^ 2 + t₃ * u ^ 3 + t₄ * u ^ 4 + t₅ * u ^ 5 + t₆ * u ^ 6) :
    c₅ * σ ^ 6 = t₀ ∧ c₅ * σ ^ 5 = t₁ ∧ c₃ * σ ^ 5 = t₂ ∧ c₁ * σ ^ 3 = t₃ ∧
      c₂ * σ ^ 3 = t₄ ∧ c₄ * σ = t₅ ∧ c₄ = t₆ := by
  have E := expand hcu hF hG h
  obtain ⟨e₀, e₁, e₂, e₃, e₄, e₅, e₆⟩ := seven_terms hu (a₀ := c₅ * σ ^ 6 - t₀)
    (a₁ := c₅ * σ ^ 5 - t₁) (a₂ := c₃ * σ ^ 5 - t₂) (a₃ := c₁ * σ ^ 3 - t₃)
    (a₄ := c₂ * σ ^ 3 - t₄) (a₅ := c₄ * σ - t₅) (a₆ := c₄ - t₆)
    (by push_cast at E ⊢; linear_combination ht - E)
  exact ⟨sub_eq_zero.1 e₀, sub_eq_zero.1 e₁, sub_eq_zero.1 e₂, sub_eq_zero.1 e₃,
    sub_eq_zero.1 e₄, sub_eq_zero.1 e₅, sub_eq_zero.1 e₆⟩

/-- The statement for abstract `ū, F, G` satisfying the three defining identities. -/
theorem main {u cu F G : ℂ} (hu : u ∉ Qbar) {σ : ↥Qbar} (hσ : σ ≠ 0)
    (hcu : cu * u = σ * σ) (hF : F * (σ * σ * σ) = u ^ 3 + σ * u ^ 2)
    (hG : G * u ^ 3 = σ ^ 3 + σ ^ 2 * u) :
    LinearIndependent (↥Qbar) ![1, u, cu, F, G] ∧
      u ^ 2 ∉ Submodule.span Qbar ({1, u, cu, F, G} : Set ℂ) ∧
      cu ^ 2 ∉ Submodule.span Qbar ({1, u, cu, F, G} : Set ℂ) ∧
      ∀ b ∈ Qbar, b ≠ 0 → (u - b)⁻¹ ∉ Submodule.span Qbar ({1, u, cu, F, G} : Set ℂ) := by
  refine ⟨?_, fun hw => ?_, fun hw => ?_, fun b hb hb0 hw => ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    simp [Fin.sum_univ_five, Subfield.smul_def] at hg
    obtain ⟨e₀, -, e₂, e₃, e₄, -, e₆⟩ := core hu (w := 0) (c₁ := g 0) (c₂ := g 1) (c₃ := g 2)
      (c₄ := g 3) (c₅ := g 4) (t₀ := 0) (t₁ := 0) (t₂ := 0) (t₃ := 0)
      (t₄ := 0) (t₅ := 0) (t₆ := 0) hcu hF hG (by linear_combination -hg) (by simp)
    intro i
    fin_cases i
    · exact (mul_eq_zero.1 e₃).resolve_right (pow_ne_zero 3 hσ)
    · exact (mul_eq_zero.1 e₄).resolve_right (pow_ne_zero 3 hσ)
    · exact (mul_eq_zero.1 e₂).resolve_right (pow_ne_zero 5 hσ)
    · exact e₆
    · exact (mul_eq_zero.1 e₀).resolve_right (pow_ne_zero 6 hσ)
  · obtain ⟨c₁, c₂, c₃, c₄, c₅, h⟩ := coeffs hw
    obtain ⟨-, -, -, -, -, e₅, e₆⟩ := core hu (t₀ := 0) (t₁ := 0) (t₂ := 0) (t₃ := 0)
      (t₄ := 0) (t₅ := σ ^ 3) (t₆ := 0) hcu hF hG h (by push_cast; ring)
    have : σ ^ 3 = 0 := by linear_combination -e₅ + σ * e₆
    exact pow_ne_zero 3 hσ this
  · obtain ⟨c₁, c₂, c₃, c₄, c₅, h⟩ := coeffs hw
    obtain ⟨e₀, e₁, -, -, -, -, -⟩ := core hu (t₀ := 0) (t₁ := σ ^ 7) (t₂ := 0) (t₃ := 0)
      (t₄ := 0) (t₅ := 0) (t₆ := 0) hcu hF hG h
      (by push_cast; linear_combination (σ : ℂ) ^ 3 * u * (cu * u + σ * σ) * hcu)
    have : σ ^ 8 = 0 := by linear_combination e₀ - σ * e₁
    exact pow_ne_zero 8 hσ this
  · obtain ⟨c₁, c₂, c₃, c₄, c₅, h⟩ := coeffs hw
    obtain ⟨β, rfl⟩ : ∃ β : ↥Qbar, (β : ℂ) = b := ⟨⟨b, hb⟩, rfl⟩
    have hβ0 : β ≠ 0 := by rintro rfl; exact hb0 rfl
    have hub : (u - β) * (u - β)⁻¹ = 1 :=
      mul_inv_cancel₀ (sub_ne_zero.2 fun e => hu (by rw [e]; exact β.2))
    have := root_eval hu (σ := σ) (β := β) (expand hcu hF hG h)
      (by linear_combination (σ : ℂ) ^ 3 * u ^ 3 * hub)
    exact mul_ne_zero (pow_ne_zero 3 hσ) (pow_ne_zero 3 hβ0) this

end R14_cubicExcl

open DiazModulus R14_cubicExcl in
theorem solution
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u) :
    LinearIndependent (↥Qbar) ![1, u, conj u, (u ^ 3 / (s * s * s) + u ^ 2 / (s * s)), (conj u ^ 3 / (s * s * s) + conj u ^ 2 / (s * s))] ∧
      u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u, (u ^ 3 / (s * s * s) + u ^ 2 / (s * s)), (conj u ^ 3 / (s * s * s) + conj u ^ 2 / (s * s))} : Set ℂ) ∧
      conj u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u, (u ^ 3 / (s * s * s) + u ^ 2 / (s * s)), (conj u ^ 3 / (s * s * s) + conj u ^ 2 / (s * s))} : Set ℂ) ∧
      ∀ b ∈ Qbar, b ≠ 0 → (u - b)⁻¹ ∉ Submodule.span Qbar ({1, u, conj u, (u ^ 3 / (s * s * s) + u ^ 2 / (s * s)), (conj u ^ 3 / (s * s * s) + conj u ^ 2 / (s * s))} : Set ℂ) := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Subfield.zero_mem _)
  have hcu0 : conj u ≠ 0 := (map_ne_zero _).2 hu0
  obtain ⟨σ, rfl⟩ : ∃ σ : ↥Qbar, (σ : ℂ) = s := ⟨⟨s, hs⟩, rfl⟩
  have hs0 : (σ : ℂ) ≠ 0 := by
    intro h
    rw [h] at hss
    exact mul_ne_zero hu0 hcu0 (by rw [← hss]; ring)
  have hσ : σ ≠ 0 := by rintro rfl; exact hs0 rfl
  have hcu : conj u * u = σ * σ := by rw [hss]; ring
  have hF : (u ^ 3 / (σ * σ * σ) + u ^ 2 / (σ * σ)) * (σ * σ * σ) = u ^ 3 + σ * u ^ 2 := by
    field_simp
  have hG : (conj u ^ 3 / (σ * σ * σ) + conj u ^ 2 / (σ * σ)) * u ^ 3 =
      σ ^ 3 + σ ^ 2 * u := by
    field_simp
    linear_combination ((conj u * u) ^ 2 + conj u * u * σ ^ 2 + σ ^ 4 +
      σ * u * (conj u * u + σ ^ 2)) * hcu
  exact main hu hσ hcu hF hG
