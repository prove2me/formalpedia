-- Prove2me | solution 1 for FairChores.ExpensiveChore.oo_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:24:31.134099+00:00
-- url     : https://prove2.me/submissions/b2157e9c-7fba-44d4-905e-979d6ffb52d9

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresExamples
import Theorems.Thm_FairChores_cbarSum_empty
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.ExpensiveChore
namespace FairChores.ExpensiveChore
theorem _root_.solution : oo.Valid pp := by
  refine ⟨by simp [oo], by simp [oo], ?_, by simp [oo], ?_⟩
  · simp only [oo]
    decide
  · simp [oo, pp]
    norm_num
end FairChores.ExpensiveChore
