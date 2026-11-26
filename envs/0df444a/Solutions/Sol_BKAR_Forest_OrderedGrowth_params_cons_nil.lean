-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.params_cons_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:30:06.531262+00:00
-- url     : https://prove2.me/submissions/2a4944c7-d49f-4e81-91ec-8abc9025564d

import Definitions.Def_BKAR_OrderedSimplex
import Definitions.Def_BKAR_OrderedParams
import Theorems.Thm_BKAR_OrderedSimplexParams_tail


set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution {F F' G : Forest V} {e : Edge V}
    {order : List (Edge V)} (step : EdgeExtension F F' e)
    (tail : OrderedGrowth F' order G) (u : F.EdgeParam → ℝ) :
    (OrderedGrowth.cons step tail).params u [] =
      tail.params (step.extendParam u 0) [] :=
  rfl
end BKAR.Forest.OrderedGrowth
