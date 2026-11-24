-- Prove2me | solution 1 for FairChores.ExpensiveChore.cbarSum_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:24:06.400822+00:00
-- url     : https://prove2.me/submissions/446f79de-c348-41b8-a66d-fa2df3d85ac8

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresExamples
import Theorems.Thm_FairChores_ExpensiveChore_cbar_eq
import Theorems.Thm_FairChores_cbarSum_empty
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.ExpensiveChore
namespace FairChores.ExpensiveChore
theorem _root_.solution : cbarSum cc pp Finset.univ = 6 := by
  simp [cbarSum, cbar_eq]
end FairChores.ExpensiveChore
