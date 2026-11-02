-- Prove2me | solution 1 for DiazModulus.configuration_ratio_quadratic_of_not_degree_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-01T09:30:11.746191+00:00
-- url     : https://prove2.me/submissions/22b31611-47dd-4b69-bd57-ae445d6a7333

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_rational_space_configuration_coprime_ratio
import Theorems.Thm_DiazModulus_two_by_three_configuration_ratio_degree_le_two
import Theorems.Thm_DiazModulus_mobius_ratio_configuration_u_multiplier_triple

open Complex ComplexConjugate

/-! # Without a degree-one configuration, every configuration ratio has degree two

`DiazModulus.rational_space_configuration_coprime_ratio` writes `x₁/x₀ = p(u)/q(u)` with `p, q`
coprime of degree at least one; `DiazModulus.two_by_three_configuration_ratio_degree_le_two` bounds
the degree by two; and degree one is excluded by
`DiazModulus.mobius_ratio_configuration_u_multiplier_triple`, which would produce the free triple
`t ⊆ W ∩ u⁻¹W` forbidden by `hD1`. -/

open DiazModulus in
open Polynomial in
theorem solution (u : ℂ) (hu : u ∉ Qbar) (W : Submodule (↥Qbar) ℂ) [FiniteDimensional (↥Qbar) W]
    (hW : Module.finrank (↥Qbar) W ≤ 5) (h1 : (1 : ℂ) ∈ W) (hu1 : u ∈ W) (hui : u⁻¹ ∈ W)
    (hrat : ∀ w ∈ W, w ∈ IntermediateField.adjoin Qbar ({u} : Set ℂ))
    (hD1 : ¬ (∃ t : Fin 3 → ℂ, LinearIndependent (↥Qbar) t ∧ ∀ j, t j ∈ W ∧ u * t j ∈ W))
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x)
    (hy : LinearIndependent (↥Qbar) y) (hxy : ∀ i j, x i * y j ∈ W) :
    ∃ p q : (↥Qbar)[X], IsCoprime p q ∧ max p.natDegree q.natDegree = 2 ∧ x 1 * aeval u q = x 0 * aeval u p := by
  obtain ⟨p, q, hcop, h1d, hpq⟩ :=
    DiazModulus.rational_space_configuration_coprime_ratio u hu W hrat x y hx hy hxy
  have h2 := DiazModulus.two_by_three_configuration_ratio_degree_le_two u hu W hW h1 hu1 hui x y hx hy hxy
    p q hcop h1d hpq
  refine ⟨p, q, hcop, ?_, hpq⟩
  by_contra hne
  exact hD1 (DiazModulus.mobius_ratio_configuration_u_multiplier_triple u hu W x y hx hy hxy p q hcop
    (by omega) hpq)
