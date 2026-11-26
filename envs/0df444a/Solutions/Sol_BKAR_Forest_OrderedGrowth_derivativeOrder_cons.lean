-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.derivativeOrder_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:38:07.484827+00:00
-- url     : https://prove2.me/submissions/a25650d5-8a5e-4574-bb8f-9829de39b6b2

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
    (tail : OrderedGrowth F' order G) :
    (OrderedGrowth.cons step tail).derivativeOrder =
      tail.derivativeOrder ++ [e] := by
  rw [derivativeOrder, derivativeOrder, List.reverse_cons]
end BKAR.Forest.OrderedGrowth
