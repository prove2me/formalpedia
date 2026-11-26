-- Prove2me | solution 1 for BKAR.orderedSimplexIntegralAux_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:31:08.314288+00:00
-- url     : https://prove2.me/submissions/27df3510-c629-4ed7-b076-48d04ec5336d

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex

set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]
namespace BKAR
theorem _root_.solution (top : ℝ) :
    ∀ (order : List (Edge V)) {f g : List ℝ → ℝ},
      (∀ ts, f ts = g ts) →
        orderedSimplexIntegralAux top order f =
          orderedSimplexIntegralAux top order g
  | [], _, _, hfg => hfg []
  | _ :: order, f, g, hfg => by
      apply intervalIntegral.integral_congr
      intro t _
      exact solution t order
        (f := fun ts => f (t :: ts))
        (g := fun ts => g (t :: ts))
        (fun ts => hfg (t :: ts))
end BKAR
