-- Prove2me | solution 1 for DiazModulus.real_pencil_quartic_configuration_invisible_to_four_dimensional_extensions
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:06:46.158725+00:00
-- url     : https://prove2.me/submissions/e99e997a-65b7-4475-9c25-b4ff1260eb58

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_conj_stable_real_pencil_space_carries_two_by_three_configuration
import Theorems.Thm_DiazModulus_real_pencil_quartic_space_excludes_squares_and_reciprocals
import Theorems.Thm_DiazModulus_circle_point_extension_two_by_three_configuration_iff

open Complex ComplexConjugate

/-! # The real-pencil quartic configuration needs the whole space

Let `u ∉ Q̄`, `s ∈ Q̄` real with `s² = u ū`, `F = u²/s² + s²/u²`, and
`W = span_Q̄ {1, u, ū, F, F/(s + u)}`. Put `H₀ = Q̄ + Q̄u + Q̄ū`.

* `F` is real: `ū = s²/u` and `s̄ = s` give `F̄ = s²/u² + u²/s² = F`. The five generators are
  `Q̄`-free (`real_pencil_quartic_space_excludes_squares_and_reciprocals`), so the real-pencil
  node with `λ = 1` (`conj_stable_real_pencil_space_carries_two_by_three_configuration`) says
  that `W` is conjugation-stable and carries a `2 × 3` configuration.
* No `H₀ + Q̄w` with `w ∈ W`, `w ∉ H₀`, does. `H₀ + Q̄w ≤ W`. By Theorem B
  (`circle_point_extension_two_by_three_configuration_iff`, `u ū = s²` algebraic) a configuration
  there puts `w` in `H₀ + Q̄t` with `t = u²`, `t = ū²` or `t = (u − b)⁻¹`, `b ∈ Q̄ \ {0}`. As
  `w ∉ H₀`, exchange puts `t` in `H₀ + Q̄w ≤ W`, against
  `real_pencil_quartic_space_excludes_squares_and_reciprocals`.
-/

namespace R11_quarticInvisible

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

/-- `H₀ + Q̄w ≤ W` for `w ∈ W`, when `W` is spanned by `1, u, ū` and two more numbers. -/
theorem span_four_le {u w f g : ℂ}
    (hw : w ∈ Submodule.span Qbar ({1, u, conj u, f, g} : Set ℂ)) :
    Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) ≤
      Submodule.span Qbar ({1, u, conj u, f, g} : Set ℂ) := by
  refine Submodule.span_le.2 fun x hx => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact Submodule.subset_span (by simp)
  · exact Submodule.subset_span (by simp)
  · exact Submodule.subset_span (by simp)
  · exact hw

end R11_quarticInvisible

open DiazModulus R11_quarticInvisible in
theorem solution
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u) :
    (∀ w ∈ Submodule.span Qbar ({1, u, conj u, (u ^ 2 / (s * s) + s * s / u ^ 2), (u ^ 2 / (s * s) + s * s / u ^ 2) / (s + 1 * u)} : Set ℂ), conj w ∈ Submodule.span Qbar ({1, u, conj u, (u ^ 2 / (s * s) + s * s / u ^ 2), (u ^ 2 / (s * s) + s * s / u ^ 2) / (s + 1 * u)} : Set ℂ)) ∧
      (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, (u ^ 2 / (s * s) + s * s / u ^ 2), (u ^ 2 / (s * s) + s * s / u ^ 2) / (s + 1 * u)} : Set ℂ)) ∧
      ∀ w ∈ Submodule.span Qbar ({1, u, conj u, (u ^ 2 / (s * s) + s * s / u ^ 2), (u ^ 2 / (s * s) + s * s / u ^ 2) / (s + 1 * u)} : Set ℂ),
        w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) →
        ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧
          LinearIndependent (↥Qbar) y ∧
          ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Subfield.zero_mem _)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hu0 ((map_ne_zero _).2 hu0) (by rw [← hss]; ring)
  have hcu : conj u = s * s / u := by rw [eq_div_iff hu0]; linear_combination -hss
  have hF : conj (u ^ 2 / (s * s) + s * s / u ^ 2) = u ^ 2 / (s * s) + s * s / u ^ 2 := by
    rw [map_add, map_div₀, map_div₀, map_pow, map_mul, hsr, hcu]
    field_simp
    ring
  obtain ⟨hind, hsq, hcsq, hinv⟩ :=
    DiazModulus.real_pencil_quartic_space_excludes_squares_and_reciprocals u s hu hs hsr hss
  obtain ⟨hconj, hconf⟩ :=
    DiazModulus.conj_stable_real_pencil_space_carries_two_by_three_configuration u s hu hs hsr hss
      1 (one_mem _) (by simp) _ hF hind
  refine ⟨hconj, hconf, ?_⟩
  intro w hw hw0 hconfw
  have hρ : IsAlgebraic ℚ (u * conj u) := mem_Qbar_iff.1 (by rw [← hss]; exact mul_mem hs hs)
  have hle := span_four_le hw
  rcases (DiazModulus.circle_point_extension_two_by_three_configuration_iff u w hu hρ hw0).1
    hconfw with h | h | ⟨b, hb, hb0, h⟩
  · exact hsq (hle (exchange hw0 h))
  · exact hcsq (hle (exchange hw0 h))
  · exact hinv b hb hb0 (hle (exchange hw0 h))
