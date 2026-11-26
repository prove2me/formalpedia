-- Prove2me | solution 1 for BKAR.orderedSimplexIntegralAux_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:28:06.058491+00:00
-- url     : https://prove2.me/submissions/fe2db4e5-4973-4896-95ee-5e2ee2f92d21

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex

set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]
namespace BKAR
theorem _root_.solution (top : ℝ) (e : Edge V)
    (order : List (Edge V)) (f : List ℝ → ℝ) :
    orderedSimplexIntegralAux top (e :: order) f =
      ∫ t in 0..top,
        orderedSimplexIntegralAux t order (fun ts => f (t :: ts)) :=
  rfl
end BKAR
