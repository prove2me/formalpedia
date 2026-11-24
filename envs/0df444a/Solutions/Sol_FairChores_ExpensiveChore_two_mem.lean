-- Prove2me | solution 1 for FairChores.ExpensiveChore.two_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:26:34.247914+00:00
-- url     : https://prove2.me/submissions/59d4deff-a785-4402-8262-9c9d59c0b2cc

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresExamples
import Theorems.Thm_FairChores_ExpensiveChore_oo_valid
import Theorems.Thm_FairChores_cbarSum_empty
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.ExpensiveChore
namespace FairChores.ExpensiveChore
theorem _root_.solution : (2:ℝ) ∈ MMSset 3 cc pp :=
  ⟨oo, oo_valid, fun j => by simp [cost, oo]⟩
end FairChores.ExpensiveChore
