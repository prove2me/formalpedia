-- Prove2me | solution 1 for BKAR.Forest.isAcyclicEdgeSet_insert_of_mem_activeEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:25:55.690856+00:00
-- url     : https://prove2.me/submissions/57d8a27b-a897-4f32-9a8c-fffb4f81e07d

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
import Theorems.Thm_BKAR_Forest_not_inSameComponent_of_mem_activeEdges
import Theorems.Thm_BKAR_Forest_not_mem_edges_of_mem_activeEdges
import Theorems.Thm_BKAR_Forest_acyclic_insert_iff_edge

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V)
    {e : Edge V} (he : e ∈ F.activeEdges) :
    IsAcyclicEdgeSet (insert e F.edges) :=
  (F.acyclic_insert_iff_edge (F.not_mem_edges_of_mem_activeEdges he)).mpr
    (F.not_inSameComponent_of_mem_activeEdges he)
end BKAR.Forest
