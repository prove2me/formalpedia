-- Prove2me | solution 1 for FairSelling.vbarSum_restrict_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:53:51.011881+00:00
-- url     : https://prove2.me/submissions/b4a04952-3c60-4847-8ec3-b9a7589cc82d

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (R B : Finset G) (hB : B ⊆ R) :
    vbarSum (restrictVal R w) (restrictVal R p) B = vbarSum w p B := by
  unfold vbarSum vbar
  refine Finset.sum_congr rfl (fun g hg => ?_)
  rw [restrictVal_mem R w (hB hg), restrictVal_mem R p (hB hg)]
end FairSelling
