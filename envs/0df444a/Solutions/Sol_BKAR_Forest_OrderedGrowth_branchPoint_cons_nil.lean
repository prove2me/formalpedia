-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.branchPoint_cons_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:18:32.394661+00:00
-- url     : https://prove2.me/submissions/d2f9427b-9b1f-456e-8694-4771d7fbd5ec

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_OrderedSimplexParams_tail


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution {F F' G : Forest V} {e : Edge V}
    {order : List (Edge V)} (step : EdgeExtension F F' e)
    (tail : OrderedGrowth F' order G) (u : F.EdgeParam → ℝ) :
    (OrderedGrowth.cons step tail).branchPoint u [] =
      tail.branchPoint (step.extendParam u 0) [] :=
  rfl
end BKAR.Forest.OrderedGrowth
