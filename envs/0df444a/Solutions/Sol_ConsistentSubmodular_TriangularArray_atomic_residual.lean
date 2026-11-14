-- Prove2me | solution 1 for ConsistentSubmodular.TriangularArray.atomic_residual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:28.256546+00:00
-- url     : https://prove2.me/submissions/8a877442-1304-433d-b62b-7cc5d2ec4f00

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_ArrayCompletion

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace TriangularArray

variable {m : ℕ} (M : TriangularArray m)

theorem coverage_singleton (j i : Fin (m + 1)) :
    (∑ a, if i ∈ (M.coverage j).labels a then (M.coverage j).weight a else 0) =
      M.length i j := by
  have h := (M.coverage j).value_eq {i}
  rw [finiteMaximum_singleton i (fun i => M.length i j) (M.nonnegative i j)] at h
  have hmem (a) : ((M.coverage j).labels a ∩ {i}).Nonempty ↔ i ∈ (M.coverage j).labels a := by
    constructor
    · rintro ⟨x, hx⟩
      have hxi := Finset.mem_singleton.mp (Finset.mem_inter.mp hx).2
      simpa [hxi] using (Finset.mem_inter.mp hx).1
    · intro hi
      exact ⟨i, Finset.mem_inter.mpr ⟨hi, Finset.mem_singleton_self i⟩⟩
  simpa only [hmem] using h.symm

end TriangularArray

end ConsistentSubmodular

end

end

section

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.TriangularArray
variable {m : ℕ} (M : TriangularArray m)

theorem solution (i t : Fin (m + 1)) :
    M.toAtomic.residual i t = ∑ j, if t ≤ j then M.length i j else 0 := by
  change (∑ a, if t ≤ (M.atomEquiv.symm a).1 ∧
      i ∈ (M.coverage (M.atomEquiv.symm a).1).labels (M.atomEquiv.symm a).2
    then (M.coverage (M.atomEquiv.symm a).1).weight (M.atomEquiv.symm a).2 else 0) = _
  rw [M.atomEquiv.symm.sum_comp (fun a : M.AtomIndex =>
    if t ≤ a.1 ∧ i ∈ (M.coverage a.1).labels a.2 then (M.coverage a.1).weight a.2 else 0)]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : t ≤ j
  · simpa only [hj, true_and, ite_true] using M.coverage_singleton j i
  · simp [hj]

end
