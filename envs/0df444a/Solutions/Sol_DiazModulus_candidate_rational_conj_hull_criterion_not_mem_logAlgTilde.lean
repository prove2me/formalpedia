-- Prove2me | solution 1 for DiazModulus.candidate_rational_conj_hull_criterion_not_mem_logAlgTilde
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-23T11:55:51.057077+00:00
-- url     : https://prove2.me/submissions/d0664da0-0ac6-450d-960a-75e240fe4c66

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_rational_conj_hull_two_by_three_configuration_iff
import Theorems.Thm_DiazModulus_hermite_lindemann_holds
import Theorems.Thm_DiazModulus_logAlg_conj_stable
import Theorems.Thm_DiazModulus_logAlgTilde_conj_stable

open Complex ComplexConjugate

/-! # At a candidate, a rational `z` whose hull meets Theorem F's criterion is not in `ℒ̃`

Under Roy's strong six exponentials hypothesis `hSSE`, let `u` be a candidate and `z ∈ Q̄(u)` with
hull `W = span_Q̄ {1, u, ū, z, z̄}` satisfying the right-hand side of Theorem F
(`rational_conj_hull_two_by_three_configuration_iff`): dimension 4 with `z ∈ span(1, u, ū, (u − a)⁻¹)`
for some `a ∈ Q̄` with `a ā = u ū`, or dimension 5 with a degree-one multiplier triple or one of the
two degree-two cyclic shapes. Then `z ∉ ℒ̃`.

By Hermite–Lindemann `u ∉ Q̄`, and `u ū = |u|²` is algebraic since `|u|` is. Theorem F then puts a
`2 × 3` configuration in `W`. If `z ∈ ℒ̃`, then `W ≤ ℒ̃`: `1 ∈ ℒ̃`, `u ∈ ℒ` since `exp u` is algebraic,
`ū ∈ ℒ` (`logAlg_conj_stable`) and `z̄ ∈ ℒ̃` (`logAlgTilde_conj_stable`). The configuration then lies
in `ℒ̃`, against `hSSE`. -/

namespace R21a_K

open DiazModulus

/-- The space `Q̄ + Q̄u + Q̄ū + Q̄z + Q̄z̄` lies in `ℒ̃` once `u ∈ ℒ` and `z ∈ ℒ̃`. -/
theorem span_le_logAlgTilde {u z : ℂ} (huL : u ∈ LogAlg) (hz : z ∈ LogAlgTilde) :
    Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) ≤ LogAlgTilde :=
  Submodule.span_le.2 (Set.insert_subset_iff.2 ⟨Submodule.subset_span (Set.mem_insert _ _),
    Set.insert_subset_iff.2 ⟨Submodule.subset_span (Set.mem_insert_of_mem _ huL),
      Set.insert_subset_iff.2
        ⟨Submodule.subset_span (Set.mem_insert_of_mem _ (logAlg_conj_stable u huL)),
        Set.insert_subset_iff.2 ⟨hz, Set.singleton_subset_iff.2 (logAlgTilde_conj_stable z hz)⟩⟩⟩⟩)

/-- `u ū = |u|²` is algebraic once `|u|` is. -/
theorem mul_conj_alg {u : ℂ} (h : IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ)) : IsAlgebraic ℚ (u * conj u) := by
  rw [Complex.mul_conj']
  exact h.pow 2

end R21a_K

open DiazModulus R21a_K in
open Polynomial in
theorem solution
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    (u z : ℂ) (hcand : IsCandidate u) (hz : z ∈ IntermediateField.adjoin Qbar ({u} : Set ℂ))
    (hF : (Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ)) = 4 ∧ ∃ a ∈ Qbar, a * conj a = u * conj u ∧
          z ∈ Submodule.span Qbar ({1, u, conj u, (u - a)⁻¹} : Set ℂ)) ∨
      (Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ)) = 5 ∧
        ((∃ t : Fin 3 → ℂ, LinearIndependent (↥Qbar) t ∧ ∀ j, t j ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) ∧ u * t j ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ)) ∨ (∃ P' Q' S₁ S₂ : (↥Qbar)[X], IsCoprime P' Q' ∧ max P'.natDegree Q'.natDegree = 2 ∧
        S₁.natDegree ≤ 2 ∧ S₂.natDegree ≤ 2 ∧
        Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q' * aeval u S₁ / (u * aeval u P'),
          aeval u P' * aeval u S₂ / (u * aeval u Q')} : Set ℂ)) ∨
        (∃ P' Q' S₁ S₂ : (↥Qbar)[X], IsCoprime P' Q' ∧ max P'.natDegree Q'.natDegree = 2 ∧
        S₁.natDegree ≤ 2 ∧ S₂.natDegree ≤ 2 ∧
        Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q' * aeval u S₁ / (u * aeval u P'),
          aeval u Q' * (aeval u Q' * aeval u S₁ + aeval u P' * aeval u S₂) / (u * aeval u P' ^ 2)} :
            Set ℂ))))) :
    z ∉ LogAlgTilde := by
  intro hzL
  have hu : u ∉ Qbar := fun hq => hermite_lindemann_holds u hcand.1 (mem_Qbar_iff.1 hq) hcand.2.2
  obtain ⟨x, y, hx, hy, hxy⟩ :=
    (rational_conj_hull_two_by_three_configuration_iff u z hu (mul_conj_alg hcand.2.1) hz).2 hF
  exact hSSE x y hx hy fun i j => span_le_logAlgTilde hcand.2.2 hzL (hxy i j)
