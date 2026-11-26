-- Prove2me | solution 1 for C6BipartiteDomination.corona_core_neighbor_finset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:08:39.056687+00:00
-- url     : https://prove2.me/submissions/a8b87e84-1955-4067-88a7-959bb1099192

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
namespace C6BipartiteDomination
theorem _root_.solution (i : Fin 5) :
    Finset.univ.filter (fun u => coronaGraph.Adj (Sum.inl i) u) =
      (Finset.univ.erase i).image (fun j : Fin 5 => (Sum.inl j : CoronaVertex)) ∪
        ({Sum.inr (i, 0), Sum.inr (i, 1)} : Finset CoronaVertex) := by
  classical
  ext v
  cases v with
  | inl j =>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp [coronaGraph, coronaAdj, Finset.mem_filter, Finset.mem_union,
        Finset.mem_image, eq_comm]
  | inr p =>
      rcases p with ⟨j, q⟩
      fin_cases q <;>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] <;>
        simp [coronaGraph, coronaAdj, Finset.mem_union, Finset.mem_image, eq_comm]
end C6BipartiteDomination
