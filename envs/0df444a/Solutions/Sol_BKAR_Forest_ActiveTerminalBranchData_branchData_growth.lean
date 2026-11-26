-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.branchData_growth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:25:13.214589+00:00
-- url     : https://prove2.me/submissions/1679fd74-ca43-4fb0-ab55-cd459d73e2d0

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}
namespace BKAR.Forest.ActiveTerminalBranchData
theorem _root_.solution (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    data.branchData.growth e = (data.growth e).growth :=
  rfl
end BKAR.Forest.ActiveTerminalBranchData
