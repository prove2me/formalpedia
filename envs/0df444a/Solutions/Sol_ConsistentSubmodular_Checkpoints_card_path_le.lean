-- Prove2me | solution 1 for ConsistentSubmodular.Checkpoints.card_path_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:54.826861+00:00
-- url     : https://prove2.me/submissions/9ff6f507-0a67-4889-8cc6-e7fe2f3c6e12

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Reduction_CheckpointSchedule

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Checkpoints

variable {n : ℕ}

theorem pre_subset (D : Finset (Fin n)) (r : ℕ) : pre D r ⊆ D := by
  intro x hx
  exact Finset.mem_toList.mp (List.mem_of_mem_take (List.mem_toFinset.mp hx))

theorem card_pre (D : Finset (Fin n)) (r : ℕ) : (pre D r).card = min r D.card := by
  rw [pre, List.toFinset_card_of_nodup (List.Nodup.sublist (List.take_sublist r _)
    D.nodup_toList), List.length_take, Finset.length_toList]

end ConsistentSubmodular.Checkpoints

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Checkpoints
variable {n : ℕ}

theorem solution (C A : Finset (Fin n)) (r : ℕ) :
    (path C A r).card ≤ max C.card A.card := by
  have hu := Finset.card_union_le (C \ pre (C \ A) r) (pre (A \ C) r)
  have hs : (C \ pre (C \ A) r).card = C.card - (pre (C \ A) r).card :=
    Finset.card_sdiff_of_subset ((pre_subset _ _).trans Finset.sdiff_subset)
  have h1 := card_pre (C \ A) r
  have h2 := card_pre (A \ C) r
  have h3 := Finset.card_sdiff_add_card_inter C A
  have h4 := Finset.card_sdiff_add_card_inter A C
  have h5 : (C ∩ A).card = (A ∩ C).card := by rw [Finset.inter_comm]
  have h6 : (pre (C \ A) r).card ≤ C.card :=
    Finset.card_le_card ((pre_subset _ _).trans Finset.sdiff_subset)
  rw [path]
  omega

end
