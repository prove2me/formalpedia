-- Prove2me | solution 1 for FairChores.ExpensiveChore.cbar_gt_two_MMS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:29:11.527823+00:00
-- url     : https://prove2.me/submissions/57ed3570-ba6a-43c9-8686-290d239e7641

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresExamples
import Theorems.Thm_FairChores_ExpensiveChore_cbar_eq
import Theorems.Thm_FairChores_ExpensiveChore_MMS_eq

set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.ExpensiveChore
namespace FairChores.ExpensiveChore
theorem _root_.solution : 2 * MMS 3 cc pp < cbar cc pp 0 := by
  rw [MMS_eq, cbar_eq]
  norm_num
end FairChores.ExpensiveChore
