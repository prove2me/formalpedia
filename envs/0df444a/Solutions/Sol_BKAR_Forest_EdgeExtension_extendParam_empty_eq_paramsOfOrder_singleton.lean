-- Prove2me | solution 1 for BKAR.Forest.EdgeExtension.extendParam_empty_eq_paramsOfOrder_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:27:50.731319+00:00
-- url     : https://prove2.me/submissions/1bdc49b0-7dce-4d92-91d5-89578d8c2615

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_Forest_paramsOfOrder_empty
import Theorems.Thm_BKAR_Forest_EdgeExtension_extendParam_eq_paramsOfOrder_cons

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e : Edge V}
namespace BKAR.Forest.EdgeExtension
theorem _root_.solution
    (h : EdgeExtension (Forest.empty V) F' e) (t : ℝ) :
    h.extendParam emptyParam t = F'.paramsOfOrder [e] [t] := by
  rw [h.extendParam_eq_paramsOfOrder_cons [] [] emptyParam t
    (paramsOfOrder_empty [] []).symm]
end BKAR.Forest.EdgeExtension
