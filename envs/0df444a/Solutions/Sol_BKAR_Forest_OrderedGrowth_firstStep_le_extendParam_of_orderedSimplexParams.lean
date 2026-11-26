-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.firstStep_le_extendParam_of_orderedSimplexParams
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:18:03.514973+00:00
-- url     : https://prove2.me/submissions/93baebb7-b234-4662-99f6-8cea94caf0d5

import Definitions.Def_BKAR_OrderedSimplex
import Definitions.Def_BKAR_OrderedParams
import Theorems.Thm_BKAR_Forest_EdgeExtension_le_extendParam_of_le
import Theorems.Thm_BKAR_OrderedSimplexParams_head_le_top


set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution
    (h : OrderedGrowth F (e :: order) G) (u : F.EdgeParam → ℝ)
    {top t : ℝ} {ts : List ℝ}
    (hts : OrderedSimplexParams top (t :: ts))
    (hu : ∀ e : F.EdgeParam, top ≤ u e) :
    ∀ e' : h.tailForest.EdgeParam, t ≤ h.firstStep.extendParam u t e' :=
  h.firstStep.le_extendParam_of_le u hts.head_le_top hu
end BKAR.Forest.OrderedGrowth
