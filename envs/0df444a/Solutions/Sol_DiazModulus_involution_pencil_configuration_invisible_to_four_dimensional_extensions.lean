-- Prove2me | solution 1 for DiazModulus.involution_pencil_configuration_invisible_to_four_dimensional_extensions
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:24:50.40198+00:00
-- url     : https://prove2.me/submissions/ba5cd59e-f742-4d71-aa7f-1152f23852e6

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_involution_pencil_space_carries_two_by_three_configuration
import Theorems.Thm_DiazModulus_involution_pencil_space_excludes_squares_and_reciprocals
import Theorems.Thm_DiazModulus_circle_point_extension_two_by_three_configuration_iff

open Complex ComplexConjugate

/-! # The involution-pencil configuration needs the whole space

Let `u ∉ Q̄` with `ρ = u ū` algebraic, and let `W` be the involution-pencil space: the `Q̄`-span of
`1, u, u⁻¹` and of `q₁(u)ⁱq₂(u)³⁻ⁱ / (u l₁(u) l₂(u))`, `i = 0..3`. Put `H₀ = Q̄ + Q̄u + Q̄ū`.

* `W` carries a `2 × 3` configuration (`involution_pencil_space_carries_two_by_three_configuration`).
* No `H₀ + Q̄w` with `w ∈ W`, `w ∉ H₀`, does. Since `ū = ρ u⁻¹` and `ρ ≠ 0`, `H₀ + Q̄w ≤ W`.
  By Theorem B (`circle_point_extension_two_by_three_configuration_iff`, with `z := w`) a
  configuration there puts `w` in `H₀ + Q̄t` with `t = u²`, `t = ū²` or `t = (u − b)⁻¹`,
  `b ∈ Q̄ \ {0}`. As `w ∉ H₀`, exchange puts `t` in `H₀ + Q̄w ≤ W`. But
  `involution_pencil_space_excludes_squares_and_reciprocals` says `u²`, `u⁻²` and `(u − b)⁻¹`
  are not in `W`; and `ū² ∈ W` would give `u⁻² = ρ⁻² ū² ∈ W`.
-/

namespace R9_pencilInvisible

open DiazModulus

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

theorem span_mul_mem {S : Set ℂ} {c v : ℂ} (hc : c ∈ Qbar) (hv : v ∈ Submodule.span Qbar S) :
    c * v ∈ Submodule.span Qbar S := by
  have := Submodule.smul_mem _ (⟨c, hc⟩ : ↥Qbar) hv
  rwa [Subfield.smul_def, smul_eq_mul] at this

/-- `H₀ + Q̄w ≤ W` for every `w ∈ W`, when `W ∋ 1, u, u⁻¹` and `u ū ∈ Q̄`. -/
theorem span_four_le {u w : ℂ} {T : Set ℂ} (hρ : u * conj u ∈ Qbar)
    (hw : w ∈ Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪ T)) :
    Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) ≤
      Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪ T) := by
  have hc : conj u ∈ Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪ T) := by
    by_cases hu0 : u = 0
    · subst hu0; simp
    · have := span_mul_mem hρ (Submodule.subset_span (s := ({1, u, u⁻¹} : Set ℂ) ∪ T)
        (R := ↥Qbar) (Or.inl (by simp) : u⁻¹ ∈ ({1, u, u⁻¹} : Set ℂ) ∪ T))
      rwa [mul_comm u, mul_assoc, mul_inv_cancel₀ hu0, mul_one] at this
  refine Submodule.span_le.2 (Set.insert_subset_iff.2 ⟨Submodule.subset_span (by simp),
    Set.insert_subset_iff.2 ⟨Submodule.subset_span (by simp),
      Set.insert_subset_iff.2 ⟨hc, Set.singleton_subset_iff.2 hw⟩⟩⟩)

/-- `ū² ∈ W` forces `u⁻² ∈ W`: `u⁻² = ρ⁻² ū²`. -/
theorem inv_sq_mem {u : ℂ} {S : Set ℂ} (hu0 : u ≠ 0) (hρ : u * conj u ∈ Qbar)
    (h : conj u ^ 2 ∈ Submodule.span Qbar S) : (u ^ 2)⁻¹ ∈ Submodule.span Qbar S := by
  have := span_mul_mem (inv_mem (pow_mem hρ 2)) h
  have hc : conj u ≠ 0 := (map_ne_zero _).2 hu0
  rwa [show ((u * conj u) ^ 2)⁻¹ * conj u ^ 2 = (u ^ 2)⁻¹ by field_simp] at this

end R9_pencilInvisible

open DiazModulus R9_pencilInvisible in
theorem solution
    (u : ℂ) (hu : u ∉ Qbar) (q₁ q₂ l₁ l₂ : Polynomial ↥Qbar)
    (hq₁ : q₁.natDegree ≤ 2) (hq₂ : q₂.natDegree ≤ 2) (hdeg : q₁.natDegree = 2 ∨ q₂.natDegree = 2)
    (hcop : IsCoprime q₁ q₂)
    (hl₁ : l₁ ∈ Submodule.span ↥Qbar ({q₁, q₂} : Set (Polynomial ↥Qbar))) (hl₁0 : l₁ ≠ 0)
    (hl₂ : l₂ ∈ Submodule.span ↥Qbar ({q₁, q₂} : Set (Polynomial ↥Qbar))) (hl₂0 : l₂ ≠ 0) (hρ : IsAlgebraic ℚ (u * conj u)) :
    (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪ Set.range (fun i : Fin 4 =>
        Polynomial.aeval u q₁ ^ (i : ℕ) * Polynomial.aeval u q₂ ^ (3 - (i : ℕ)) /
          (u * Polynomial.aeval u l₁ * Polynomial.aeval u l₂)))) ∧
      ∀ w ∈ Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪ Set.range (fun i : Fin 4 =>
        Polynomial.aeval u q₁ ^ (i : ℕ) * Polynomial.aeval u q₂ ^ (3 - (i : ℕ)) /
          (u * Polynomial.aeval u l₁ * Polynomial.aeval u l₂))),
        w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) →
        ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧
          LinearIndependent (↥Qbar) y ∧
          ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) := by
  have hρ' := mem_Qbar_iff.2 hρ
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Subfield.zero_mem _)
  refine ⟨DiazModulus.involution_pencil_space_carries_two_by_three_configuration
    u hu q₁ q₂ l₁ l₂ hq₁ hq₂ hdeg hcop hl₁ hl₁0 hl₂ hl₂0, ?_⟩
  intro w hw hw0 hconf
  obtain ⟨hsq, hisq, hinv⟩ := DiazModulus.involution_pencil_space_excludes_squares_and_reciprocals
    u hu q₁ q₂ l₁ l₂ hq₁ hq₂ hdeg hcop hl₁ hl₁0 hl₂ hl₂0
  have hle := span_four_le hρ' hw
  rcases (DiazModulus.circle_point_extension_two_by_three_configuration_iff u w hu hρ hw0).1
    hconf with h | h | ⟨b, hb, hb0, h⟩
  · exact hsq (hle (exchange hw0 h))
  · exact hisq (inv_sq_mem hu0 hρ' (hle (exchange hw0 h)))
  · exact hinv b hb hb0 (hle (exchange hw0 h))
