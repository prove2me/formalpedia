-- Prove2me | solution 1 for BKAR.Forest.ActiveExtension.consGrowth_branchPoint_of_initial_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:20:30.824006+00:00
-- url     : https://prove2.me/submissions/670f6deb-409d-44cf-82eb-89ba3d477113

import Definitions.Def_BKAR_OrderedTerminal
import Definitions.Def_BKAR_OrderedRecursion
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchPoint_of_initial_mem
import Theorems.Thm_BKAR_OrderedSimplexParams_tail


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveExtension
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.ActiveExtension
theorem _root_.solution (h : ActiveExtension F e)
    (tail : OrderedGrowth h.forest order G)
    (u : F.EdgeParam → ℝ) (ts : List ℝ) {e' : Edge V}
    (he' : e' ∈ F.edges) :
    (h.consGrowth tail).branchPoint u ts e' = u ⟨e', he'⟩ :=
  (h.consGrowth tail).branchPoint_of_initial_mem u ts he'
end BKAR.Forest.ActiveExtension
