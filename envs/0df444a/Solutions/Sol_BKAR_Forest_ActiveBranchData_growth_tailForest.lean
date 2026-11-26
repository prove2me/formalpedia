-- Prove2me | solution 1 for BKAR.Forest.ActiveBranchData.growth_tailForest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:22:09.89226+00:00
-- url     : https://prove2.me/submissions/2f2a4050-7ac2-44b7-ac61-8bfe9d5431b7

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder

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
    (data.growth e).tailForest = (data.extension e).forest :=
  rfl
end BKAR.Forest.ActiveBranchData
