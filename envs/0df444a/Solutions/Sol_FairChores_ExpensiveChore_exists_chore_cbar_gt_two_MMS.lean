-- Prove2me | solution 1 for FairChores.ExpensiveChore.exists_chore_cbar_gt_two_MMS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:54:27.773124+00:00
-- url     : https://prove2.me/submissions/6bc5f290-cf26-4095-bc5d-12eed1123d17

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresExamples
import Theorems.Thm_FairChores_ExpensiveChore_cbar_gt_two_MMS

set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.ExpensiveChore
namespace FairChores.ExpensiveChore
theorem _root_.solution :
    ∃ (c p : Fin 1 → ℝ) (t : Fin 1), 2 * MMS 3 c p < cbar c p t :=
  ⟨cc, pp, 0, cbar_gt_two_MMS⟩
end FairChores.ExpensiveChore
