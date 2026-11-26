-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.singleton_branchData
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:24:52.511297+00:00
-- url     : https://prove2.me/submissions/cf5eb198-4572-48cf-a43e-66be5da4a257

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
theorem _root_.solution
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅) :
    (singleton extensions hterm).branchData =
      ActiveBranchData.singleton extensions :=
  rfl
end BKAR.Forest.ActiveTerminalBranchData
