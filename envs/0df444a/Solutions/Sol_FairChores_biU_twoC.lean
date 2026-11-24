-- Prove2me | solution 1 for FairChores.biU_twoC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:47:39.15849+00:00
-- url     : https://prove2.me/submissions/bbd79138-82fc-48e8-93fc-6439064d70a6

import Mathlib
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_ChoresPreAlloc
import Definitions.Def_RequestProject_ChoresTwoAgents
import Theorems.Thm_FairChores_cbarSum_empty
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
omit [Fintype T]
namespace FairChores
theorem _root_.solution (A : Fin 2 → Finset T) : Finset.univ.biUnion A = A 0 ∪ A 1 := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union, Fin.exists_fin_two]
end FairChores
