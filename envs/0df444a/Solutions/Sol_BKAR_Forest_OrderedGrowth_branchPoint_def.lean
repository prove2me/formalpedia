-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.branchPoint_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:31:59.155503+00:00
-- url     : https://prove2.me/submissions/170b31be-e850-4a2b-960f-1282b3933d36

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ts : List ℝ) :
    h.branchPoint u ts = G.standardInterp (h.params u ts) :=
  rfl
end BKAR.Forest.OrderedGrowth
