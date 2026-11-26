-- Prove2me | solution 1 for BKAR.OrderedSimplexParams.tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:28:04.246362+00:00
-- url     : https://prove2.me/submissions/f14450c9-f472-48a6-87d9-ba9dc2c719ad

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex

set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.OrderedSimplexParams
namespace BKAR.OrderedSimplexParams
theorem _root_.solution {top t : ℝ} {ts : List ℝ}
    (h : OrderedSimplexParams top (t :: ts)) :
    OrderedSimplexParams t ts :=
  h.2.2
end BKAR.OrderedSimplexParams
