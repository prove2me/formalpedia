-- Prove2me | solution 1 for BKAR.orderedSimplexIntegral_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:28:11.328901+00:00
-- url     : https://prove2.me/submissions/6ba54eb9-bcf7-419f-9d27-5188827b92a1

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex

set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]
namespace BKAR
theorem _root_.solution (f : List ℝ → ℝ) :
    orderedSimplexIntegral ([] : List (Edge V)) f = f [] :=
  rfl
end BKAR
