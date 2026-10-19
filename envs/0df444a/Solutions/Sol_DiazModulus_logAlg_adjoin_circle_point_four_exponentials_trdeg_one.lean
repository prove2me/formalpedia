-- Prove2me | solution 1 for DiazModulus.logAlg_adjoin_circle_point_four_exponentials_trdeg_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T17:52:19.198928+00:00
-- url     : https://prove2.me/submissions/184be9e0-6a3e-45f0-9823-f1db5f2f18c3

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_logAlg_adjoin_circle_point_trdeg_le_one_trichotomy
import Theorems.Thm_DiazModulus_four_exponentials_trdeg_one
import Theorems.Thm_DiazModulus_four_exp_barrier_of_no_quadratic_relation
import Theorems.Thm_Transcendence_quadratic_coeffs_eq_zero_of_transcendental

open Complex ComplexConjugate

/-! # The four exponentials theorem in transcendence degree one, for `ℒ_u = ℒ + ℚu + ℚū`

Apply the trichotomy `logAlg_adjoin_circle_point_trdeg_le_one_trichotomy` to the four entries
`lᵢⱼ ∈ ℒ_u` of the singular matrix, whose `ℚ`-algebra has transcendence degree at most one.
- (A) All `lᵢⱼ` lie in `ℒ`: then every `exp lᵢⱼ` is algebraic, and `four_exponentials_trdeg_one`
  gives the conclusion verbatim.
- (B) All `lᵢⱼ = rᵢⱼ e` lie on one `ℚ`-line: `e ≠ 0`, so `r₁₁ r₂₂ = r₁₂ r₂₁`, and the rational pair
  `(r₂₁, -r₁₁) ≠ 0` makes the rows dependent.
- (C) All `lᵢⱼ = pᵢⱼ u + qᵢⱼ ū`: then `four_exp_barrier_of_no_quadratic_relation` with `e = (u, ū)`
  applies, once `u, ū` satisfy no rational quadratic relation. A relation
  `a u² + b uū + c ū² = 0` times `u²` reads `a (u²)² + bρ u² + cρ² = 0` with `ρ = uū` algebraic and
  non-zero; `u²` is transcendental, so `quadratic_coeffs_eq_zero_of_transcendental` makes
  `a = b = c = 0`, which is the alternating condition the barrier asks for.
-/

namespace R19_D4
open DiazModulus

/-- `u` and `ū` satisfy no rational quadratic relation when `u` is transcendental and `uū` is
algebraic: only alternating coefficient matrices vanish at `(u, ū)`. -/
theorem no_quadratic_relation (u : ℂ) (hρ : IsAlgebraic ℚ (u * conj u))
    (hu : Transcendental ℚ u) (F : Fin 2 → Fin 2 → ℚ)
    (hF : ∑ k, ∑ l, (F k l : ℂ) * (![u, conj u] k * ![u, conj u] l) = 0) :
    ∀ k l, F k l + F l k = 0 := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ isAlgebraic_zero)
  have hρ0 : u * conj u ≠ 0 := mul_ne_zero hu0 ((map_ne_zero _).mpr hu0)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hF
  have hq : (F 0 0 : ℂ) * (u ^ 2) ^ 2 + ((F 0 1 + F 1 0 : ℚ) : ℂ) * (u * conj u) * u ^ 2
      + (F 1 1 : ℂ) * (u * conj u) ^ 2 = 0 := by
    push_cast
    linear_combination u ^ 2 * hF
  obtain ⟨h2, h1, h0⟩ := Transcendence.quadratic_coeffs_eq_zero_of_transcendental
    (hu.pow two_pos) ((isAlgebraic_ratCast ℚ _).mul (hρ.pow 2))
    ((isAlgebraic_ratCast ℚ _).mul hρ) (isAlgebraic_ratCast ℚ _) hq
  have e00 : F 0 0 = 0 := by exact_mod_cast h2
  have e01 : F 0 1 + F 1 0 = 0 := by exact_mod_cast (mul_eq_zero.mp h1).resolve_right hρ0
  have e11 : F 1 1 = 0 := by
    exact_mod_cast (mul_eq_zero.mp h0).resolve_right (pow_ne_zero 2 hρ0)
  intro k l
  fin_cases k <;> fin_cases l
  · simp [e00]
  · simpa using e01
  · simpa [add_comm] using e01
  · simp [e11]

end R19_D4

open DiazModulus R19_D4 in
theorem solution
    (u : ℂ) (hρ : IsAlgebraic ℚ (u * conj u))
    (hu : Transcendental (Subfield.closure (LogAlgTilde : Set ℂ)) u)
    (l₁₁ l₁₂ l₂₁ l₂₂ : ℂ)
    (h₁₁ : l₁₁ ∈ (Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ)))
    (h₁₂ : l₁₂ ∈ (Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ)))
    (h₂₁ : l₂₁ ∈ (Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ)))
    (h₂₂ : l₂₂ ∈ (Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ)))
    (n₁₁ : l₁₁ ≠ 0) (n₁₂ : l₁₂ ≠ 0) (n₂₁ : l₂₁ ≠ 0) (n₂₂ : l₂₂ ≠ 0)
    (hdet : l₁₁ * l₂₂ = l₁₂ * l₂₁)
    (htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({l₁₁, l₁₂, l₂₁, l₂₂} : Set ℂ)) ≤ 1) :
    (∃ a b : ℚ, ¬(a = 0 ∧ b = 0) ∧ (a : ℂ) * l₁₁ + (b : ℂ) * l₂₁ = 0 ∧ (a : ℂ) * l₁₂ + (b : ℂ) * l₂₂ = 0)
    ∨ (∃ a b : ℚ, ¬(a = 0 ∧ b = 0) ∧ (a : ℂ) * l₁₁ + (b : ℂ) * l₁₂ = 0 ∧ (a : ℂ) * l₂₁ + (b : ℂ) * l₂₂ = 0) := by
  have hS : ∀ z ∈ ({l₁₁, l₁₂, l₂₁, l₂₂} : Set ℂ),
      z ∈ (Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ)) := by
    rintro z (rfl | rfl | rfl | rfl) <;> assumption
  have m₁₁ : l₁₁ ∈ ({l₁₁, l₁₂, l₂₁, l₂₂} : Set ℂ) := by simp
  have m₁₂ : l₁₂ ∈ ({l₁₁, l₁₂, l₂₁, l₂₂} : Set ℂ) := by simp
  have m₂₁ : l₂₁ ∈ ({l₁₁, l₁₂, l₂₁, l₂₂} : Set ℂ) := by simp
  have m₂₂ : l₂₂ ∈ ({l₁₁, l₁₂, l₂₁, l₂₂} : Set ℂ) := by simp
  rcases logAlg_adjoin_circle_point_trdeg_le_one_trichotomy u hρ hu _ hS htr with hA | ⟨e, hB⟩ | hC
  · -- (A) all entries in `ℒ`
    exact four_exponentials_trdeg_one l₁₁ l₁₂ l₂₁ l₂₂ (hA _ m₁₁) (hA _ m₁₂) (hA _ m₂₁) (hA _ m₂₂)
      n₁₁ n₁₂ n₂₁ n₂₂ hdet htr
  · -- (B) all entries on one rational line `ℚe`
    obtain ⟨r₁₁, e₁₁⟩ := hB _ m₁₁
    obtain ⟨r₁₂, e₁₂⟩ := hB _ m₁₂
    obtain ⟨r₂₁, e₂₁⟩ := hB _ m₂₁
    obtain ⟨r₂₂, e₂₂⟩ := hB _ m₂₂
    have hr : r₁₁ ≠ 0 := by rintro rfl; exact n₁₁ (by rw [e₁₁]; simp)
    have he : e ≠ 0 := by rintro rfl; exact n₁₁ (by rw [e₁₁]; simp)
    have hdr : (r₁₁ : ℂ) * r₂₂ = r₁₂ * r₂₁ := by
      have h : ((r₁₁ : ℂ) * r₂₂ - r₁₂ * r₂₁) * (e * e) = 0 := by
        rw [e₁₁, e₁₂, e₂₁, e₂₂] at hdet; linear_combination hdet
      linear_combination (mul_eq_zero.mp h).resolve_right (mul_ne_zero he he)
    left
    refine ⟨r₂₁, -r₁₁, fun h => hr (neg_eq_zero.mp h.2), ?_, ?_⟩
    · rw [e₁₁, e₂₁]; push_cast; ring
    · rw [e₁₂, e₂₂]; push_cast; linear_combination (-e) * hdr
  · -- (C) all entries in `ℚu + ℚū`
    obtain ⟨p₁₁, q₁₁, e₁₁⟩ := hC _ m₁₁
    obtain ⟨p₁₂, q₁₂, e₁₂⟩ := hC _ m₁₂
    obtain ⟨p₂₁, q₂₁, e₂₁⟩ := hC _ m₂₁
    obtain ⟨p₂₂, q₂₂, e₂₂⟩ := hC _ m₂₂
    have key := four_exp_barrier_of_no_quadratic_relation ![u, conj u]
      (no_quadratic_relation u hρ (hu.of_tower_top ℚ))
      ![![![p₁₁, q₁₁], ![p₁₂, q₁₂]], ![![p₂₁, q₂₁], ![p₂₂, q₂₂]]] ![![l₁₁, l₁₂], ![l₂₁, l₂₂]]
      (by
        intro i j
        fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two, e₁₁, e₁₂, e₂₁, e₂₂])
      (by simpa using hdet)
    rcases key with ⟨a, b, hab, h⟩ | ⟨a, b, hab, h⟩
    · exact Or.inl ⟨a, b, hab, by simpa using h 0, by simpa using h 1⟩
    · exact Or.inr ⟨a, b, hab, by simpa using h 0, by simpa using h 1⟩
