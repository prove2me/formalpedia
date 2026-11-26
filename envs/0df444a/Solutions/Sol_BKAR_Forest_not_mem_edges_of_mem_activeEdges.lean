-- Prove2me | solution 1 for BKAR.Forest.not_mem_edges_of_mem_activeEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:25:02.647718+00:00
-- url     : https://prove2.me/submissions/2d82d0ce-93e8-4e84-9fa3-8d3c18a4255b

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
import Theorems.Thm_BKAR_Forest_not_inSameComponent_of_mem_activeEdges
import Theorems.Thm_BKAR_Forest_not_mem_edges_of_not_inSameComponent

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) {e : Edge V}
    (he : e ∈ F.activeEdges) :
    e ∉ F.edges :=
  F.not_mem_edges_of_not_inSameComponent
    (F.not_inSameComponent_of_mem_activeEdges he)
end BKAR.Forest
