-- Prove2me | solution 1 for BKAR.orderedSimplexParams_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:28:17.28737+00:00
-- url     : https://prove2.me/submissions/88905a24-53af-454d-a710-030df97347a1

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex

set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]
namespace BKAR
theorem _root_.solution (top t : ℝ) (ts : List ℝ) :
    OrderedSimplexParams top (t :: ts) ↔
      0 ≤ t ∧ t ≤ top ∧ OrderedSimplexParams t ts :=
  Iff.rfl
end BKAR
