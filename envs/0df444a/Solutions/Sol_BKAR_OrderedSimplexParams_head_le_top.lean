-- Prove2me | solution 1 for BKAR.OrderedSimplexParams.head_le_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:29:44.221804+00:00
-- url     : https://prove2.me/submissions/96e6bbcc-d67e-466b-a1b9-9bf8893f9368

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
    t ≤ top :=
  h.2.1
end BKAR.OrderedSimplexParams
