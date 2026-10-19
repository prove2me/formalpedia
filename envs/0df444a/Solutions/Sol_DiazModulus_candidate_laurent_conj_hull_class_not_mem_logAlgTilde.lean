-- Prove2me | solution 1 for DiazModulus.candidate_laurent_conj_hull_class_not_mem_logAlgTilde
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T14:29:49.536071+00:00
-- url     : https://prove2.me/submissions/d9dfad71-87bc-42b1-a7f8-4a1dfb4f63bb

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_laurent_conj_hull_two_by_three_configuration_iff
import Theorems.Thm_DiazModulus_laurent_conj_hull_class_finrank_eq_five
import Theorems.Thm_DiazModulus_hermite_lindemann_holds
import Theorems.Thm_DiazModulus_logAlg_conj_stable
import Theorems.Thm_DiazModulus_logAlgTilde_conj_stable

open Complex ComplexConjugate

/-! # At a candidate, a polynomial in `u` and `ū` of class (P), (Q) or (R) is not in `ℒ̃`

Under Roy's strong six exponentials hypothesis `hSSE`, let `u` be a candidate, `s ∈ Q̄` with
`s² = u ū`, and `z = Σ_{|j| ≤ k} c_j (u/s)^j` (`c_j ∈ Q̄`) with hull `W = span_Q̄ {1, u, ū, z, z̄}` in
class (P), (Q) or (R). Then `z ∉ ℒ̃`.

By Hermite–Lindemann `u ∉ Q̄`. The class forces `dim W = 5`
(`laurent_conj_hull_class_finrank_eq_five`), so Theorem E
(`laurent_conj_hull_two_by_three_configuration_iff`) puts a `2 × 3` configuration in `W`. If `z ∈ ℒ̃`,
then `W ≤ ℒ̃`: `1 ∈ ℒ̃`, `u ∈ ℒ` since `exp u` is algebraic, `ū ∈ ℒ` (`logAlg_conj_stable`) and
`z̄ ∈ ℒ̃` (`logAlgTilde_conj_stable`). The configuration then lies in `ℒ̃`, against `hSSE`. -/

namespace R18_EC

open DiazModulus

/-- The space `Q̄ + Q̄u + Q̄ū + Q̄z + Q̄z̄` lies in `ℒ̃` once `u ∈ ℒ` and `z ∈ ℒ̃`. -/
theorem span_le_logAlgTilde {u z : ℂ} (huL : u ∈ LogAlg) (hz : z ∈ LogAlgTilde) :
    Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) ≤ LogAlgTilde :=
  Submodule.span_le.2 (Set.insert_subset_iff.2 ⟨Submodule.subset_span (Set.mem_insert _ _),
    Set.insert_subset_iff.2 ⟨Submodule.subset_span (Set.mem_insert_of_mem _ huL),
      Set.insert_subset_iff.2
        ⟨Submodule.subset_span (Set.mem_insert_of_mem _ (logAlg_conj_stable u huL)),
        Set.insert_subset_iff.2 ⟨hz, Set.singleton_subset_iff.2 (logAlgTilde_conj_stable z hz)⟩⟩⟩⟩)

end R18_EC

open DiazModulus R18_EC in
theorem solution
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    (u s : ℂ) (hcand : IsCandidate u) (hs : s ∈ Qbar) (hss : s * s = u * conj u)
    (k : ℕ) (c : ℤ → ℂ) (hc : ∀ j, c j ∈ Qbar)
    (hcls : (∃ α β : ℂ, α ∈ Qbar ∧ β ∈ Qbar ∧ (α ≠ 0 ∨ β ≠ 0) ∧ α * u ^ 2 + β * u ^ 3 ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ)) ∨
      (∃ e β ζ : ℂ, e ∈ Qbar ∧ β ∈ Qbar ∧ ζ ∈ Qbar ∧ e * conj e = 1 ∧ β * conj β = 1 ∧
        ζ = -(β * e ^ 2 * conj ζ) ∧
        Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ) =
          Submodule.span Qbar ({1, u, conj u, conj (u / s) ^ 2 + e * (u / s) ^ 2, β * conj (u / s) ^ 3 + ζ * (u / s) ^ 2 + e * (u / s) ^ 3} : Set ℂ)) ∨
      (∃ κ : ℂ, κ ∈ Qbar ∧ κ * conj κ = 1 ∧ ∃ G : Polynomial ↥Qbar, G.coeff 0 = 0 ∧ 2 ≤ G.natDegree ∧
        Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ) =
          Submodule.span Qbar ({1, u, conj u, Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G), conj (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G))} : Set ℂ))) :
    (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j) ∉ LogAlgTilde := by
  intro hzL
  have hu : u ∉ Qbar := fun hq => hermite_lindemann_holds u hcand.1 (mem_Qbar_iff.1 hq) hcand.2.2
  obtain ⟨x, y, hx, hy, hxy⟩ := (laurent_conj_hull_two_by_three_configuration_iff u s hu hs hss k c hc).2
    ⟨laurent_conj_hull_class_finrank_eq_five u s hu hs hss k c hcls, hcls⟩
  exact hSSE x y hx hy fun i j => span_le_logAlgTilde hcand.2.2 hzL (hxy i j)
