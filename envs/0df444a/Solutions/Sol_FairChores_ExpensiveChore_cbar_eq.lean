-- Prove2me | solution 1 for FairChores.ExpensiveChore.cbar_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:18:52.982031+00:00
-- url     : https://prove2.me/submissions/488601b1-6ebb-4065-9006-1de312828014

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresExamples

set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.ExpensiveChore
namespace FairChores.ExpensiveChore
theorem _root_.solution : ∀ t, cbar cc pp t = 6 := by
  intro t; norm_num [cbar, cc, pp]
end FairChores.ExpensiveChore
