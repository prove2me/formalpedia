-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.branchPoint_of_initial_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:38:43.690804+00:00
-- url     : https://prove2.me/submissions/8ff29e78-db1b-4635-bc41-574f6a6ced33

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchPoint_initial

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ts : List ℝ) {e : Edge V} (he : e ∈ F.edges) :
    h.branchPoint u ts e = u ⟨e, he⟩ :=
  h.branchPoint_initial u ts ⟨e, he⟩
end BKAR.Forest.OrderedGrowth
