-- Prove2me | solution 1 for EmmonsTardiness.SPT.totalTardiness_cons_shift
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T04:49:00.218655+00:00
-- url     : https://prove2.me/submissions/d788cfcc-4992-4f03-9379-93b0e98992b9

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_EmmonsTardiness_SPT_Model

set_option autoImplicit false

open MooreLateJobs in
theorem c25bd689_compl_cons_ne {ι : Type*} [DecidableEq ι] (p : ι → ℝ) (k : ι) (l' : List ι)
    (i : ι) (hi : i ≠ k) :
    Shared.completionTime p (k :: l') i = p k + Shared.completionTime p l' i := by
  unfold Shared.completionTime Shared.completionAt
  rw [List.idxOf_cons_ne _ (Ne.symm hi)]
  simp [List.take_succ_cons]

open MooreLateJobs in
theorem c25bd689_compl_cons_self {ι : Type*} [DecidableEq ι] (p : ι → ℝ) (k : ι) (l' : List ι) :
    Shared.completionTime p (k :: l') k = p k := by
  unfold Shared.completionTime Shared.completionAt
  simp

open EmmonsTardiness.SPT MooreLateJobs in
theorem solution {ι : Type*} [DecidableEq ι] (p d : ι → ℝ) (J : Finset ι)
    (k : ι) (hk : k ∈ J) (l' : List ι) (hl' : Shared.IsSchedule (J.erase k) l') :
    totalTardiness p d J (k :: l') =
      max 0 (p k - d k) + totalTardiness p (fun i => d i - p k) (J.erase k) l' := by
  unfold totalTardiness
  rw [← Finset.add_sum_erase J _ hk]
  congr 1
  · simp [tardiness, c25bd689_compl_cons_self]
  · apply Finset.sum_congr rfl
    intro i hi
    have hik : i ≠ k := Finset.ne_of_mem_erase hi
    simp only [tardiness, c25bd689_compl_cons_ne p k l' i hik]
    congr 1
    ring
