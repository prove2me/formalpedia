-- Prove2me | solution 1 for BKAR.OrderedSimplexParams.nonneg_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:37:32.216808+00:00
-- url     : https://prove2.me/submissions/e0bebab1-5116-405a-b277-b2de4544298e

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex
import Theorems.Thm_BKAR_OrderedSimplexParams_head_nonneg
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.OrderedSimplexParams
namespace BKAR.OrderedSimplexParams
theorem _root_.solution :
    ∀ {top : ℝ} {ts : List ℝ} {t : ℝ},
      OrderedSimplexParams top ts → t ∈ ts → 0 ≤ t
  | _, [], _, _, ht => by
      cases ht
  | _, x :: xs, t, h, ht => by
      rw [List.mem_cons] at ht
      cases ht with
      | inl htx =>
          rw [htx]
          exact h.head_nonneg
      | inr htxs =>
          exact solution h.tail htxs
end BKAR.OrderedSimplexParams
