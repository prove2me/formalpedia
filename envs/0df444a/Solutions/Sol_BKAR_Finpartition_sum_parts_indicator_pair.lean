-- Prove2me | solution 1 for BKAR.Finpartition.sum_parts_indicator_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:09:19.750851+00:00
-- url     : https://prove2.me/submissions/849db1e9-8032-4f5c-b22f-8200cf3d591d

import Mathlib.Order.Partition.Finpartition
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Threshold
import Definitions.Def_BKAR_ThresholdComponents
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
attribute [local simp] BKAR.Forest.paramValue_of_mem
attribute [local simp] BKAR.Forest.pathMin_cons
attribute [local simp] BKAR.Forest.pathMin_nil



set_option autoImplicit false
open BKAR
open scoped BigOperators
open BKAR.Finpartition
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section
namespace BKAR.Finpartition
theorem _root_.solution
    (P : Finpartition (Finset.univ : Finset V)) (r : ℝ) (z w : V) :
    (∑ c : {c : Finset V // c ∈ P.parts},
        if z ∈ c.1 ∧ w ∈ c.1 then r else 0) =
      if w ∈ P.part z then r else 0 := by
  classical
  let cz : {c : Finset V // c ∈ P.parts} :=
    ⟨P.part z, (P.part_mem (a := z)).2 (Finset.mem_univ z)⟩
  by_cases hw : w ∈ P.part z
  · rw [Finset.sum_eq_single cz]
    · simp [cz, hw]
    · intro c _ hc
      have hz_not : z ∉ c.1 := by
        intro hz
        apply hc
        apply Subtype.ext
        exact (P.part_eq_of_mem c.2 hz).symm
      simp [hz_not]
    · intro hcz
      exact False.elim (hcz (Finset.mem_univ cz))
  · rw [if_neg hw]
    apply Finset.sum_eq_zero
    intro c _
    by_cases hz : z ∈ c.1
    · have hpart : P.part z = c.1 := P.part_eq_of_mem c.2 hz
      have hwc : w ∉ c.1 := by
        intro hwc
        exact hw (by rwa [hpart])
      simp [hz, hwc]
    · simp [hz]
end BKAR.Finpartition
