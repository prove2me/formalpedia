-- Prove2me | solution 1 for DiazModulus.rational_space_two_by_three_configuration_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-23T07:25:10.800662+00:00
-- url     : https://prove2.me/submissions/eb24d270-ff99-4221-ad54-f13544db3ca0

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_degree_two_configuration_normal_form
import Theorems.Thm_DiazModulus_quadratic_two_orbit_space_carries_two_by_three_configuration
import Theorems.Thm_DiazModulus_quadratic_cyclic_space_carries_two_by_three_configuration
import Theorems.Thm_DiazModulus_rational_space_configuration_coprime_ratio
import Theorems.Thm_DiazModulus_mobius_ratio_configuration_u_multiplier_triple
import Theorems.Thm_DiazModulus_two_by_three_configuration_ratio_degree_le_two

open Complex ComplexConjugate

/-! # Configurations in a five-dimensional subspace of `Q̄(u)` containing `1, u, 1/u`

(⇒) Given a configuration `x ⊗ y` in `W`, `rational_space_configuration_coprime_ratio` writes
`x₁/x₀ = p(u)/q(u)` with `p, q` coprime and `max(deg p, deg q) ≥ 1`, and
`two_by_three_configuration_ratio_degree_le_two` (`dim W ≤ 5`, `1, u, u⁻¹ ∈ W`) bounds that degree
by `2`. In degree `1`, `mobius_ratio_configuration_u_multiplier_triple` gives three free `t` with
`t, u t ∈ W` (case D1). In degree `2`, Theorem NF (`degree_two_configuration_normal_form`) gives
D1, or `W` equal to one of the two canonical spans D2a, D2b.
(⇐) In case D1 the configuration is `(1, u) ⊗ t`: `1, u` are free because `u ∉ Q̄`, and the
products are `t` and `u t`. In cases D2a and D2b, `W` is the canonical span, which has dimension
`5`, and `quadratic_two_orbit_space_carries_two_by_three_configuration` resp.
`quadratic_cyclic_space_carries_two_by_three_configuration` supply the configuration.
-/

namespace R20_C17

open DiazModulus

theorem smul_eq (a : ↥Qbar) (z : ℂ) : a • z = (a : ℂ) * z := rfl

/-- `1, u` are free over `Q̄` when `u ∉ Q̄`. -/
theorem one_u_free {u : ℂ} (hu : u ∉ Qbar) : LinearIndependent (↥Qbar) ![(1 : ℂ), u] := by
  refine LinearIndependent.pair_iff.2 fun s t hst => ?_
  rw [smul_eq, smul_eq, mul_one] at hst
  have ht : t = 0 := by
    by_contra ht0
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
    apply hu
    have hu' : u = -((s : ℂ) / t) := by
      field_simp
      linear_combination hst
    rw [hu']
    exact Qbar.neg_mem (Qbar.div_mem s.2 t.2)
  refine ⟨?_, ht⟩
  rw [ht] at hst
  have : (s : ℂ) = 0 := by simpa using hst
  exact_mod_cast this

end R20_C17

open DiazModulus R20_C17 Polynomial in
theorem solution (u : ℂ) (hu : u ∉ Qbar) (W : Submodule (↥Qbar) ℂ) [FiniteDimensional (↥Qbar) W]
    (hW : Module.finrank (↥Qbar) W = 5) (h1 : (1 : ℂ) ∈ W) (hu1 : u ∈ W) (hui : u⁻¹ ∈ W)
    (hrat : ∀ w ∈ W, w ∈ IntermediateField.adjoin Qbar ({u} : Set ℂ)) :
    (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
        ∀ i j, x i * y j ∈ W) ↔
    (∃ t : Fin 3 → ℂ, LinearIndependent (↥Qbar) t ∧ ∀ j, t j ∈ W ∧ u * t j ∈ W) ∨ (∃ P' Q' S₁ S₂ : (↥Qbar)[X], IsCoprime P' Q' ∧ max P'.natDegree Q'.natDegree = 2 ∧
        S₁.natDegree ≤ 2 ∧ S₂.natDegree ≤ 2 ∧
        W = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q' * aeval u S₁ / (u * aeval u P'),
          aeval u P' * aeval u S₂ / (u * aeval u Q')} : Set ℂ)) ∨
    (∃ P' Q' S₁ S₂ : (↥Qbar)[X], IsCoprime P' Q' ∧ max P'.natDegree Q'.natDegree = 2 ∧
        S₁.natDegree ≤ 2 ∧ S₂.natDegree ≤ 2 ∧
        W = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q' * aeval u S₁ / (u * aeval u P'),
          aeval u Q' * (aeval u Q' * aeval u S₁ + aeval u P' * aeval u S₂) / (u * aeval u P' ^ 2)} :
            Set ℂ)) := by
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    obtain ⟨p, q, hcop, hdeg, hpq⟩ :=
      DiazModulus.rational_space_configuration_coprime_ratio u hu W hrat x y hx hy hxy
    have hle := DiazModulus.two_by_three_configuration_ratio_degree_le_two u hu W hW.le h1 hu1 hui
      x y hx hy hxy p q hcop hdeg hpq
    rcases (show max p.natDegree q.natDegree = 1 ∨ max p.natDegree q.natDegree = 2 by omega)
      with h | h
    · exact Or.inl (DiazModulus.mobius_ratio_configuration_u_multiplier_triple u hu W x y hx hy hxy
        p q hcop h hpq)
    · exact DiazModulus.degree_two_configuration_normal_form u hu W hW h1 hu1 hui x y hx hy hxy
        p q hcop h hpq
  · rintro (⟨t, ht, htW⟩ | ⟨P', Q', S₁, S₂, hc, hd, h₁, h₂, rfl⟩ |
      ⟨P', Q', S₁, S₂, hc, hd, h₁, h₂, rfl⟩)
    · refine ⟨![1, u], t, one_u_free hu, ht, fun i j => ?_⟩
      fin_cases i
      · simpa using (htW j).1
      · simpa using (htW j).2
    · obtain ⟨hx, hy, hxy⟩ :=
        DiazModulus.quadratic_two_orbit_space_carries_two_by_three_configuration u hu P' Q' S₁ S₂
          hd h₁ h₂ hW
      exact ⟨_, _, hx, hy, hxy⟩
    · obtain ⟨hx, hy, hxy⟩ :=
        DiazModulus.quadratic_cyclic_space_carries_two_by_three_configuration u hu P' Q' S₁ S₂
          hd h₁ h₂ hW
      exact ⟨_, _, hx, hy, hxy⟩
