-- Prove2me | solution 1 for BKAR.OrderedSimplexParams.pairwise_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:30:05.397396+00:00
-- url     : https://prove2.me/submissions/2b86cd50-e0fb-497d-b674-347be40d26d4

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Definitions.Def_BKAR_CubePartition_MeasurePartition
import Theorems.Thm_BKAR_OrderedSimplexParams_le_head_of_mem_tail
import Theorems.Thm_BKAR_OrderedSimplexParams_tail


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.OrderedSimplexParams
namespace BKAR.OrderedSimplexParams
theorem _root_.solution :
    ∀ {top : ℝ} {ts : List ℝ},
      OrderedSimplexParams top ts →
        ts.Pairwise fun t s => s ≤ t
  | _, [], _ => by
      exact List.Pairwise.nil
  | _, t :: ts, h => by
      rw [List.pairwise_cons]
      constructor
      · intro s hs
        exact OrderedSimplexParams.le_head_of_mem_tail h hs
      · exact solution h.tail
end BKAR.OrderedSimplexParams
