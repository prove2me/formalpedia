-- Prove2me | solution 1 for BKAR.Forest.EdgeExtension.extendParam_eq_paramsOfOrder_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:26:37.141156+00:00
-- url     : https://prove2.me/submissions/3b812d4b-cdf3-4bd8-a746-3ba7ca925251

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_Forest_paramsOfOrder_cons_self
import Theorems.Thm_BKAR_Forest_paramsOfOrder_cons_of_ne
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_Forest_EdgeExtension_mem_old_of_mem_of_ne


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e : Edge V}
namespace BKAR.Forest.EdgeExtension
theorem _root_.solution
    (h : EdgeExtension F F' e) (order : List (Edge V)) (ts : List ℝ)
    (u : F.EdgeParam → ℝ) (t : ℝ)
    (hu : u = F.paramsOfOrder order ts) :
    h.extendParam u t = F'.paramsOfOrder (e :: order) (t :: ts) := by
  funext e'
  by_cases hnew : e'.val = e
  · rw [extendParam, dif_pos hnew]
    rw [show e' = ⟨e, hnew ▸ e'.property⟩ from Subtype.ext hnew]
    rw [F'.paramsOfOrder_cons_self e order t ts]
  · have hold : e'.val ∈ F.edges :=
      h.mem_old_of_mem_of_ne e'.property hnew
    rw [extendParam, dif_neg hnew]
    rw [hu, F'.paramsOfOrder_cons_of_ne order t ts e'.property hnew]
    rfl
end BKAR.Forest.EdgeExtension
