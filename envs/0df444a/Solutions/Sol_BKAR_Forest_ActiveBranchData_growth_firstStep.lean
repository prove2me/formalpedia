-- Prove2me | solution 1 for BKAR.Forest.ActiveBranchData.growth_firstStep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:22:07.094572+00:00
-- url     : https://prove2.me/submissions/7ef2fca0-5234-4e93-be3e-7edfa8407489

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
    (data.growth e).firstStep = (data.extension e).extension :=
  rfl
end BKAR.Forest.ActiveBranchData
