-- Prove2me | solution 1 for BKAR.orderedSimplexIntegral_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:28:11.816108+00:00
-- url     : https://prove2.me/submissions/95f305c1-4564-4964-a694-b1586791a5c4

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex

set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]
namespace BKAR
theorem _root_.solution (e : Edge V) (order : List (Edge V))
    (f : List ℝ → ℝ) :
    orderedSimplexIntegral (e :: order) f =
      ∫ t in 0..(1 : ℝ),
        orderedSimplexIntegralAux t order (fun ts => f (t :: ts)) :=
  rfl
end BKAR
