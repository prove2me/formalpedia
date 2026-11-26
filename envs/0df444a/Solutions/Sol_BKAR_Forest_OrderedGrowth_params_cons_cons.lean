-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.params_cons_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:30:11.03781+00:00
-- url     : https://prove2.me/submissions/77f17776-b794-4fa9-9f3d-9d034e528f04

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
    (tail : OrderedGrowth F' order G) (u : F.EdgeParam → ℝ)
    (t : ℝ) (ts : List ℝ) :
    (OrderedGrowth.cons step tail).params u (t :: ts) =
      tail.params (step.extendParam u t) ts :=
  rfl
end BKAR.Forest.OrderedGrowth
