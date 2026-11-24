-- Prove2me | solution 1 for FairChores.cbarSum_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:20:33.995963+00:00
-- url     : https://prove2.me/submissions/16e42f1b-54ef-4066-84e6-4e7862b913ba

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
theorem _root_.solution (c p : T → ℝ) {A B : Finset T} (h : Disjoint A B) :
    cbarSum c p (A ∪ B) = cbarSum c p A + cbarSum c p B := by
  simp only [cbarSum]; rw [Finset.sum_union h]
end FairChores
