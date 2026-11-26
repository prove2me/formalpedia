-- Prove2me | solution 1 for C6BipartiteDomination.corona_leaf_neighbor_finset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:08:45.081169+00:00
-- url     : https://prove2.me/submissions/86175f83-2b4d-42d5-8696-7dfac3d703bb

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
namespace C6BipartiteDomination
theorem _root_.solution (i : Fin 5) (p : Fin 2) :
    Finset.univ.filter (fun u => coronaGraph.Adj (Sum.inr (i, p)) u) =
      {Sum.inl i} := by
  classical
  ext v
  cases v with
  | inl j =>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp [coronaGraph, coronaAdj, eq_comm]
  | inr q =>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp [coronaGraph, coronaAdj]
end C6BipartiteDomination
