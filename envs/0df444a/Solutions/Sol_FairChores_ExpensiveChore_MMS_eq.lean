-- Prove2me | solution 1 for FairChores.ExpensiveChore.MMS_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:28:03.524948+00:00
-- url     : https://prove2.me/submissions/bf6a1235-ddf6-46ff-839c-62fc0cce3977

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresExamples
import Theorems.Thm_FairChores_ExpensiveChore_cbarSum_univ
import Theorems.Thm_FairChores_ExpensiveChore_two_mem
import Theorems.Thm_FairChores_MMSset_bddBelow
import Theorems.Thm_FairChores_cbarSum_univ_le_sum_cost


set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.ExpensiveChore
namespace FairChores.ExpensiveChore
theorem _root_.solution : MMS 3 cc pp = 2 := by
  refine le_antisymm ?_ ?_
  · exact csInf_le (MMSset_bddBelow (fun t => by norm_num [cc]) (by norm_num)) two_mem
  · refine le_csInf ⟨2, two_mem⟩ ?_
    rintro r ⟨o, hvalid, hle⟩
    have hsum : cbarSum cc pp Finset.univ ≤ ∑ j, cost cc o j := cbarSum_univ_le_sum_cost hvalid
    rw [cbarSum_univ] at hsum
    have h2 : ∑ j, cost cc o j ≤ 3 * r := by
      rw [Fin.sum_univ_three]
      linarith [hle 0, hle 1, hle 2]
    linarith
end FairChores.ExpensiveChore
