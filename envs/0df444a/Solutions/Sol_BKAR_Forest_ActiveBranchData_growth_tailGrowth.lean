-- Prove2me | solution 1 for BKAR.Forest.ActiveBranchData.growth_tailGrowth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:22:12.705678+00:00
-- url     : https://prove2.me/submissions/93e7e7fd-1a71-4981-9b91-ebf6ce11a014

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
    (data.growth e).tailGrowth = data.tail e :=
  rfl
end BKAR.Forest.ActiveBranchData
