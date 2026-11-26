-- Prove2me | solution 1 for BKAR.Forest.ActiveBranchData.singleton_growth_eq_singletonGrowth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:22:51.698099+00:00
-- url     : https://prove2.me/submissions/69b96151-cceb-48c4-a4b3-b83781af43c5

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
theorem _root_.solution
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (e : {e // e ∈ F.activeEdges}) :
    (singleton extensions).growth e = (extensions e).singletonGrowth :=
  rfl
end BKAR.Forest.ActiveBranchData
