-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.singleton_growth_growth_eq_singletonGrowth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:26:12.044808+00:00
-- url     : https://prove2.me/submissions/8bbef22b-6819-449d-8637-d5f132172214

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
      (extensions e).forest.activeEdges = ∅)
    (e : {e // e ∈ F.activeEdges}) :
    ((singleton extensions hterm).growth e).growth =
      (extensions e).singletonGrowth :=
  rfl
end BKAR.Forest.ActiveTerminalBranchData
