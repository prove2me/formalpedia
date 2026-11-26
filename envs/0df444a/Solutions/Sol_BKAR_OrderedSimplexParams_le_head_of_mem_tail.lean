-- Prove2me | solution 1 for BKAR.OrderedSimplexParams.le_head_of_mem_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:47:27.640653+00:00
-- url     : https://prove2.me/submissions/cb71b97b-7899-4889-a8e3-9467d99cbf78

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex
import Theorems.Thm_BKAR_OrderedSimplexParams_tail
import Theorems.Thm_BKAR_OrderedSimplexParams_le_top_of_mem

set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.OrderedSimplexParams
namespace BKAR.OrderedSimplexParams
theorem _root_.solution {top t s : ℝ} {ts : List ℝ}
    (h : OrderedSimplexParams top (t :: ts)) (hs : s ∈ ts) :
    s ≤ t :=
  le_top_of_mem h.tail hs
end BKAR.OrderedSimplexParams
