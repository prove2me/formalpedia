-- Prove2me | solution 1 for BKAR.OrderedSimplexParams.head_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:36:46.600748+00:00
-- url     : https://prove2.me/submissions/2e1ffbaf-1ecc-4b82-9e89-171f5e42d32f

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
    0 ≤ t :=
  h.1
end BKAR.OrderedSimplexParams
