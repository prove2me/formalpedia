-- Prove2me | solution 1 for BKAR.Forest.ActiveBranchData.growth_firstActiveExtension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:22:15.07992+00:00
-- url     : https://prove2.me/submissions/4f263d69-57d8-4070-bbff-c9bd7c877228

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
    (data.growth e).firstActiveExtension = data.extension e :=
  rfl
end BKAR.Forest.ActiveBranchData
