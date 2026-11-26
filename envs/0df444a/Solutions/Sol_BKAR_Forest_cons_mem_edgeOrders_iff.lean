-- Prove2me | solution 1 for BKAR.Forest.cons_mem_edgeOrders_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:50:06.113611+00:00
-- url     : https://prove2.me/submissions/8175669b-4767-4d65-918e-3210af8b8254

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_Forest_cons_mem_edgeSetOrders_iff

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V)
    {e : Edge V} {order : List (Edge V)} :
    e :: order ∈ F.edgeOrders ↔
      e ∈ F.edges ∧ order ∈ edgeSetOrders (F.edges.erase e) :=
  cons_mem_edgeSetOrders_iff F.edges
end BKAR.Forest
