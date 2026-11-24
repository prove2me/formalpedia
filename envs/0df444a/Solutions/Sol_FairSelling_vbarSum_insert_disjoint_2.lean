-- Prove2me | solution 2 for FairSelling.vbarSum_insert_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:04:41.847799+00:00
-- url     : https://prove2.me/submissions/c03a7425-7191-42b8-8d80-f0c523c62f58

import Mathlib
import Definitions.Def_RequestProject_ConfigSplit
import Definitions.Def_RequestProject_CanonicalStrict
import Definitions.Def_RequestProject_LemmaFourResidual
import Theorems.Thm_FairSelling_cashPrice_none
import Theorems.Thm_FairSelling_cashPrice_some
import Theorems.Thm_FairSelling_cashVal_none
import Theorems.Thm_FairSelling_cashVal_some
import Theorems.Thm_FairSelling_mem_optionGoods
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_vbarSum_union
attribute [local simp] FairSelling.cashPrice_none
attribute [local simp] FairSelling.cashPrice_some
attribute [local simp] FairSelling.cashVal_none
attribute [local simp] FairSelling.cashVal_some
attribute [local simp] FairSelling.mem_optionGoods
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (K : Finset G) (f : G) (hfK : f ∉ K) :
    vbarSum w p (K ∪ {f}) = vbarSum w p K + vbar w p f := by
  rw [vbarSum_union w p (Finset.disjoint_singleton_right.mpr hfK)]
  simp [vbarSum]
end FairSelling
