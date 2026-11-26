-- Prove2me | solution 1 for BKAR.Forest.standardInterp_paramsOfOrder_eq_of_edges_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:27:49.959439+00:00
-- url     : https://prove2.me/submissions/0718e949-83ad-4394-89bf-c9e10561171e

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_Forest_paramValue_paramsOfOrder_eq_of_edges_eq
import Theorems.Thm_BKAR_Forest_standardInterp_eq_of_edges_eq


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F G : Forest V) (hedges : F.edges = G.edges)
    (order : List (Edge V)) (ts : List ℝ) :
    F.standardInterp (F.paramsOfOrder order ts) =
      G.standardInterp (G.paramsOfOrder order ts) :=
  F.standardInterp_eq_of_edges_eq G
    (F.paramsOfOrder order ts) (G.paramsOfOrder order ts)
    hedges
    (F.paramValue_paramsOfOrder_eq_of_edges_eq G hedges order ts)
end BKAR.Forest
