-- Prove2me | solution 1 for DiazModulus.candidate_div_sq_sub_not_mem_logAlgTilde
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-06T07:49:19.473522+00:00
-- url     : https://prove2.me/submissions/25ad55d1-e851-45fd-9ee2-2ca98cab9ba6

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_circle_point_conjugate_pair_extension_carries_two_by_three_configuration
import Theorems.Thm_DiazModulus_hermite_lindemann_holds
import Theorems.Thm_DiazModulus_logAlg_conj_stable
import Theorems.Thm_DiazModulus_logAlgTilde_conj_stable

open Complex ComplexConjugate

/-!
# `u/(u² − a)` and `u/(u² − a)²` at a candidate

Under Roy's strong six exponentials theorem, let `u` be a candidate and `a ∈ Q̄` non-zero. Then
`u/(u² − a) ∉ ℒ̃` when `a ā ≠ (u ū)²`, and `u/(u² − a)² ∉ ℒ̃` when `a ā = (u ū)²`.

At a candidate `ρ = u ū = |u|²` is algebraic, and `u ∉ Q̄` by Hermite–Lindemann. Both `u` and
`ū` lie in `ℒ` (`logAlg_conj_stable`), and `ℒ̃` is stable under conjugation
(`logAlgTilde_conj_stable`). So if `z ∈ ℒ̃` then `W = Q̄ + Q̄u + Q̄ū + Q̄z + Q̄z̄ ≤ ℒ̃`, and the
`2 × 3` configuration that `circle_point_conjugate_pair_extension_carries_two_by_three_configuration`
puts in `W` lies in `ℒ̃`, against the strong six exponentials hypothesis.
-/

namespace R5_candidate

open DiazModulus

/-- If `z ∈ ℒ̃`, the configuration in `Q̄ + Q̄u + Q̄ū + Q̄z + Q̄z̄` lies in `ℒ̃`. -/
theorem not_mem
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    {u a z : ℂ} (hu : u ∉ Qbar) (huL : u ∈ LogAlg) (hρ : IsAlgebraic ℚ (u * conj u))
    (ha : a ∈ Qbar) (ha0 : a ≠ 0)
    (hz : (a * conj a ≠ (u * conj u) ^ 2 ∧ z = u / (u ^ 2 - a)) ∨
      (a * conj a = (u * conj u) ^ 2 ∧ z = u / (u ^ 2 - a) ^ 2)) :
    z ∉ LogAlgTilde := by
  intro hzL
  obtain ⟨x, y, hx, hy, hxy⟩ :=
    circle_point_conjugate_pair_extension_carries_two_by_three_configuration u a z hu hρ ha ha0 hz
  have hle : Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) ≤ LogAlgTilde :=
    Submodule.span_le.2 (Set.insert_subset_iff.2 ⟨Submodule.subset_span (Set.mem_insert _ _),
      Set.insert_subset_iff.2 ⟨Submodule.subset_span (Set.mem_insert_of_mem _ huL),
        Set.insert_subset_iff.2
          ⟨Submodule.subset_span (Set.mem_insert_of_mem _ (logAlg_conj_stable u huL)),
          Set.insert_subset_iff.2 ⟨hzL,
            Set.singleton_subset_iff.2 (logAlgTilde_conj_stable z hzL)⟩⟩⟩⟩)
  exact hSSE x y hx hy fun i j => hle (hxy i j)

end R5_candidate

open DiazModulus R5_candidate in
theorem solution
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    {u : ℂ} (h : IsCandidate u) {a : ℂ} (ha : a ∈ Qbar) (ha0 : a ≠ 0) :
    (a * conj a ≠ (u * conj u) ^ 2 → u / (u ^ 2 - a) ∉ LogAlgTilde) ∧
      (a * conj a = (u * conj u) ^ 2 → u / (u ^ 2 - a) ^ 2 ∉ LogAlgTilde) := by
  have huQ : u ∉ Qbar := fun hq => hermite_lindemann_holds u h.1 (mem_Qbar_iff.1 hq) h.2.2
  have hρ : IsAlgebraic ℚ (u * conj u) := by
    rw [Complex.mul_conj']
    exact mem_Qbar_iff.1 (Qbar.pow_mem (mem_Qbar_iff.2 h.2.1) 2)
  exact ⟨fun hne => not_mem hSSE huQ h.2.2 hρ ha ha0 (Or.inl ⟨hne, rfl⟩),
    fun heq => not_mem hSSE huQ h.2.2 hρ ha ha0 (Or.inr ⟨heq, rfl⟩)⟩

#print axioms solution
