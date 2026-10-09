-- Prove2me | solution 1 for DiazModulus.circle_point_two_pole_configuration_invisible_to_four_dimensional_extensions
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T09:02:14.105813+00:00
-- url     : https://prove2.me/submissions/f6df3947-5b10-460c-abb0-384c6b26399d

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_circle_point_two_pole_extension_carries_two_by_three_configuration
import Theorems.Thm_DiazModulus_circle_point_two_pole_extension_excludes_squares_and_reciprocals
import Theorems.Thm_DiazModulus_circle_point_extension_two_by_three_configuration_iff

open Complex ComplexConjugate

/-!
# A configuration through two poles needs all five dimensions

Let `u ∉ Q̄` with `ρ = u ū` algebraic, `a₁ ≠ a₂` non-zero algebraic numbers, `zᵢ = u/(u² − aᵢ)`.
Put `H₀ = Q̄ + Q̄u + Q̄ū` and `W = H₀ + Q̄z₁ + Q̄z₂`.

* `W` carries a `2 × 3` configuration
  (`circle_point_two_pole_extension_carries_two_by_three_configuration`).
* No `H₀ + Q̄w` with `w ∈ W`, `w ∉ H₀`, does. By Theorem B
  (`circle_point_extension_two_by_three_configuration_iff`, with `z := w`) a configuration there
  puts `w` in `H₀ + Q̄t` with `t = u²`, `t = ū²` or `t = 1/(u − b)`, `b ∈ Q̄ \ {0}`. As `w ∉ H₀`,
  exchange puts `t` in `H₀ + Q̄w`, which lies in `W`; and
  `circle_point_two_pole_extension_excludes_squares_and_reciprocals` says no such `t` is in `W`.
-/

namespace R7_twoPoleFiveDim

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

/-- `H₀ + Q̄w ≤ W` for every `w ∈ W`. -/
theorem span_four_le {u z₁ z₂ w : ℂ}
    (hw : w ∈ Submodule.span Qbar ({1, u, conj u, z₁, z₂} : Set ℂ)) :
    Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) ≤
      Submodule.span Qbar ({1, u, conj u, z₁, z₂} : Set ℂ) := by
  refine Submodule.span_le.2 (Set.insert_subset_iff.2 ⟨Submodule.subset_span (by simp),
    Set.insert_subset_iff.2 ⟨Submodule.subset_span (by simp),
      Set.insert_subset_iff.2 ⟨Submodule.subset_span (by simp),
        Set.singleton_subset_iff.2 hw⟩⟩⟩)

end R7_twoPoleFiveDim

open DiazModulus R7_twoPoleFiveDim in
theorem solution (u a₁ a₂ : ℂ)
    (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u)) (ha₁ : a₁ ∈ Qbar) (ha₂ : a₂ ∈ Qbar)
    (ha₁0 : a₁ ≠ 0) (ha₂0 : a₂ ≠ 0) (ha : a₁ ≠ a₂) :
    (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, u / (u ^ 2 - a₁), u / (u ^ 2 - a₂)} : Set ℂ)) ∧
      ∀ w ∈ Submodule.span Qbar ({1, u, conj u, u / (u ^ 2 - a₁), u / (u ^ 2 - a₂)} : Set ℂ),
        w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) →
        ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧
          LinearIndependent (↥Qbar) y ∧
          ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) := by
  refine ⟨circle_point_two_pole_extension_carries_two_by_three_configuration
    u a₁ a₂ hu hρ ha₁ ha₂ ha₁0 ha₂0 ha, ?_⟩
  intro w hw hw0 hconf
  obtain ⟨hsq, hcsq, hinv⟩ := circle_point_two_pole_extension_excludes_squares_and_reciprocals
    u a₁ a₂ hu hρ ha₁ ha₂ ha₁0 ha₂0 ha
  have hle := span_four_le hw
  rcases (circle_point_extension_two_by_three_configuration_iff u w hu hρ hw0).1 hconf with
    h | h | ⟨b, hb, hb0, h⟩
  · exact hsq (hle (exchange hw0 h))
  · exact hcsq (hle (exchange hw0 h))
  · exact hinv b hb hb0 (hle (exchange hw0 h))
