-- Prove2me | solution 1 for ConsistentSubmodular.exists_sharedThreshold
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:29:34.043847+00:00
-- url     : https://prove2.me/submissions/361c6900-d1b7-478b-a886-1ef150ca334d

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_SharedThreshold

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace MaximumCoverage

variable {d : ℕ} {w : Fin d → ℝ} (R : MaximumCoverage w)

theorem singleton_weight (hw : ∀ i, 0 ≤ w i) (i : Fin d) :
    (∑ a, if i ∈ R.labels a then R.weight a else 0) = w i := by
  have h := R.value_eq {i}
  rw [finiteMaximum_singleton i w (hw i)] at h
  have hmem (a) : (R.labels a ∩ {i}).Nonempty ↔ i ∈ R.labels a := by
    constructor
    · rintro ⟨x, hx⟩
      have hxi := Finset.mem_singleton.mp (Finset.mem_inter.mp hx).2
      simpa [hxi] using (Finset.mem_inter.mp hx).1
    · intro hi
      exact ⟨i, Finset.mem_inter.mpr ⟨hi, Finset.mem_singleton_self i⟩⟩
  simpa only [hmem] using h.symm

theorem total_weight : (∑ a, R.weight a) = finiteMaximum Finset.univ w := by
  simpa [R.labels_nonempty] using (R.value_eq Finset.univ).symm

end MaximumCoverage

end ConsistentSubmodular

end

end

section

open scoped BigOperators
open ConsistentSubmodular

theorem solution {d : ℕ} (z : Fin d → ℝ) (hz : ∀ t, 0 ≤ z t ∧ z t ≤ 1) :
    Nonempty (SharedThreshold z) := by
  classical
  obtain ⟨R⟩ := exists_maximumCoverage z (fun t => (hz t).1)
  let M := finiteMaximum Finset.univ z
  have hM : M ≤ 1 := finiteMaximum_le (by norm_num) (fun t _ => (hz t).2)
  refine ⟨{
    cellCount := R.atomCount + 1
    law := {
      weight := Fin.cases (1 - M) R.weight
      nonnegative := ?_
      sum_one := ?_
    }
    active := Fin.cases ∅ R.labels
    inclusion := ?_
    ordered := ?_
  }⟩
  · intro ω
    exact Fin.cases (sub_nonneg.mpr hM) (fun a => (R.weight_positive a).le) ω
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ]
    rw [R.total_weight]
    dsimp [M]
    ring
  · intro t
    unfold FiniteLaw.probability
    dsimp only
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ, Finset.notMem_empty, ite_false, zero_add]
    convert R.singleton_weight (fun t => (hz t).1) t using 2
    congr
  · intro ω
    refine Fin.cases ?_ ?_ ω
    · intro s t _ hs
      exact (Finset.notMem_empty s hs).elim
    · intro a s t hst hs
      exact R.labels_upward a s t hst hs

end
