-- Prove2me | solution 1 for DiazModulus.laurent_conj_hull_configuration_shape_iff_class
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-23T11:55:56.562222+00:00
-- url     : https://prove2.me/submissions/8469b233-3a01-4d7d-9d9a-0c55cf632c60

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_laurent_conj_hull_two_by_three_configuration_iff
import Theorems.Thm_DiazModulus_rational_conj_hull_two_by_three_configuration_iff

open Complex ComplexConjugate

/-! # Theorem F's shapes and Theorem E's classes agree on five-dimensional Laurent hulls

Let `u ∉ Q̄` with `u ū = s²`, `s ∈ Q̄`, and let `z = ∑_{|j| ≤ k} c_j (u/s)^j` be a Laurent polynomial in
`v = u/s` with algebraic coefficients, with `W = span(1, u, ū, z, z̄)` of dimension 5. Then `W` has one of
Theorem F's shapes (D1, D2a, D2b) exactly when it is in one of Theorem E's classes (P), (Q), (R).

Both sides are equivalent to "`W` carries a 2 × 3 configuration". Theorem E
(`laurent_conj_hull_two_by_three_configuration_iff`, 10.98) applies to the Laurent data directly and says
CONF ⟺ dim 5 ∧ ((P) ∨ (Q) ∨ (R)). Theorem F (`rational_conj_hull_two_by_three_configuration_iff`, 10.146)
needs `u ū` algebraic, which is `s·s ∈ Q̄`, and `z ∈ Q̄(u)`: each term `c_j (u/s)^j` lies in the
intermediate field `Q̄(u)` (closed under division and integer powers). It says
CONF ⟺ (dim 4 ∧ circle) ∨ (dim 5 ∧ (D1 ∨ D2a ∨ D2b)). With dim W = 5 the dimension-4 branch is empty,
so the two right-hand sides are equivalent.
-/

namespace R21a_A
open DiazModulus

/-- A Laurent polynomial in `u/s` with algebraic coefficients lies in `Q̄(u)`. -/
theorem laurent_mem_adjoin (u : ℂ) {s : ℂ} (hs : s ∈ Qbar) (k : ℕ) (c : ℤ → ℂ)
    (hc : ∀ j, c j ∈ Qbar) :
    (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j) ∈
      IntermediateField.adjoin Qbar ({u} : Set ℂ) := by
  have hQ : ∀ a ∈ Qbar, a ∈ IntermediateField.adjoin Qbar ({u} : Set ℂ) := fun a ha => by
    exact (IntermediateField.adjoin Qbar ({u} : Set ℂ)).algebraMap_mem ⟨a, ha⟩
  have hv : u / s ∈ IntermediateField.adjoin Qbar ({u} : Set ℂ) :=
    div_mem (IntermediateField.subset_adjoin _ _ (Set.mem_singleton u)) (hQ s hs)
  exact sum_mem fun j _ => mul_mem (hQ _ (hc j)) (zpow_mem hv j)

end R21a_A

open DiazModulus R21a_A in
open Polynomial in
theorem solution
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hss : s * s = u * conj u)
    (k : ℕ) (c : ℤ → ℂ) (hc : ∀ j, c j ∈ Qbar)
    (h5 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ)) = 5) :
    ((∃ t : Fin 3 → ℂ, LinearIndependent (↥Qbar) t ∧ ∀ j, t j ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ) ∧ u * t j ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ)) ∨ (∃ P' Q' S₁ S₂ : (↥Qbar)[X], IsCoprime P' Q' ∧ max P'.natDegree Q'.natDegree = 2 ∧
        S₁.natDegree ≤ 2 ∧ S₂.natDegree ≤ 2 ∧
        Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ) = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q' * aeval u S₁ / (u * aeval u P'),
          aeval u P' * aeval u S₂ / (u * aeval u Q')} : Set ℂ)) ∨
      (∃ P' Q' S₁ S₂ : (↥Qbar)[X], IsCoprime P' Q' ∧ max P'.natDegree Q'.natDegree = 2 ∧
        S₁.natDegree ≤ 2 ∧ S₂.natDegree ≤ 2 ∧
        Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ) = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q' * aeval u S₁ / (u * aeval u P'),
          aeval u Q' * (aeval u Q' * aeval u S₁ + aeval u P' * aeval u S₂) / (u * aeval u P' ^ 2)} :
            Set ℂ))) ↔
    ((∃ α β : ℂ, α ∈ Qbar ∧ β ∈ Qbar ∧ (α ≠ 0 ∨ β ≠ 0) ∧ α * u ^ 2 + β * u ^ 3 ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ)) ∨
      (∃ e β ζ : ℂ, e ∈ Qbar ∧ β ∈ Qbar ∧ ζ ∈ Qbar ∧ e * conj e = 1 ∧ β * conj β = 1 ∧
        ζ = -(β * e ^ 2 * conj ζ) ∧
        Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ) =
          Submodule.span Qbar ({1, u, conj u, conj (u / s) ^ 2 + e * (u / s) ^ 2, β * conj (u / s) ^ 3 + ζ * (u / s) ^ 2 + e * (u / s) ^ 3} : Set ℂ)) ∨
      (∃ κ : ℂ, κ ∈ Qbar ∧ κ * conj κ = 1 ∧ ∃ G : Polynomial ↥Qbar, G.coeff 0 = 0 ∧ 2 ≤ G.natDegree ∧
        Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ) =
          Submodule.span Qbar ({1, u, conj u, (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G)), conj (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G))} : Set ℂ))) := by
  have hρ : IsAlgebraic ℚ (u * conj u) := by
    rw [← hss]; exact mem_Qbar_iff.1 (Qbar.mul_mem hs hs)
  have hE := DiazModulus.laurent_conj_hull_two_by_three_configuration_iff u s hu hs hss k c hc
  have hF := DiazModulus.rational_conj_hull_two_by_three_configuration_iff u
    (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j) hu hρ (laurent_mem_adjoin u hs k c hc)
  constructor
  · intro hD
    exact (hE.1 (hF.2 (Or.inr ⟨h5, hD⟩))).2
  · intro hPQR
    rcases hF.1 (hE.2 ⟨h5, hPQR⟩) with ⟨h4, -⟩ | ⟨-, hD⟩
    · rw [h5] at h4; exact absurd h4 (by norm_num)
    · exact hD
