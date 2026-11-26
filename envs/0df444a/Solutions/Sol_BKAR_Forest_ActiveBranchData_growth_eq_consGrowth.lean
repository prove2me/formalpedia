-- Prove2me | solution 1 for BKAR.Forest.ActiveBranchData.growth_eq_consGrowth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:21:54.758356+00:00
-- url     : https://prove2.me/submissions/ff81742f-7274-4e2b-8ceb-67513d800c7b

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
import Theorems.Thm_BKAR_OrderedSimplexParams_tail


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveBranchData
variable {F : Forest V}
namespace BKAR.Forest.ActiveBranchData
theorem _root_.solution (data : ActiveBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    data.growth e = (data.extension e).consGrowth (data.tail e) :=
  rfl
end BKAR.Forest.ActiveBranchData
