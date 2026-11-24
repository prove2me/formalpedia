-- Prove2me | solution 1 for FairSelling.SharedProceeds.sharedTPS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:46:33.75797+00:00
-- url     : https://prove2.me/submissions/00168927-5216-4bd6-9d69-c5d39da0df5a

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxSharing
import Theorems.Thm_FairSelling_SharedProceeds_sp_nonneg
import Theorems.Thm_FairSelling_SharedProceeds_sum_vbar
import Theorems.Thm_FairSelling_TPS_le_PS
import Theorems.Thm_FairSelling_le_TPS_of_le_truncSum


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.SharedProceeds
namespace FairSelling.SharedProceeds
theorem _root_.solution : TPS 2 sv sp = 13 / 2 := by
  have hPS : PS 2 sv sp = 13 / 2 := by
    unfold PS
    rw [sum_vbar]
    norm_num
  refine le_antisymm ?_ ?_
  · have := TPS_le_PS (n := 2) sv sp sp_nonneg
    rw [hPS] at this
    exact this
  · refine le_TPS_of_le_truncSum sv sp ?_
    unfold truncSum
    rw [Fin.sum_univ_four]
    norm_num [sv, sp, Fin.ext_iff]
end FairSelling.SharedProceeds
