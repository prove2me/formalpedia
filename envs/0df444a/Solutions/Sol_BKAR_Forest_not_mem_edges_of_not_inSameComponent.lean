-- Prove2me | solution 1 for BKAR.Forest.not_mem_edges_of_not_inSameComponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:24:20.374258+00:00
-- url     : https://prove2.me/submissions/6748b004-4b66-46ca-be34-092ab94926ad

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) {e : Edge V}
    (he : ¬ F.inSameComponent e.left e.right) :
    e ∉ F.edges := by
  intro hmem
  exact he (F.edge_inSameComponent hmem)
end BKAR.Forest
