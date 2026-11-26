-- Prove2me | solution 1 for BKAR.OrderedSimplexParams.le_top_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:31:19.824076+00:00
-- url     : https://prove2.me/submissions/09072756-80df-4124-8c64-e1bc084129f9

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex
import Theorems.Thm_BKAR_OrderedSimplexParams_head_le_top
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.OrderedSimplexParams
namespace BKAR.OrderedSimplexParams
theorem _root_.solution :
    ∀ {top : ℝ} {ts : List ℝ} {t : ℝ},
      OrderedSimplexParams top ts → t ∈ ts → t ≤ top
  | _, [], _, _, ht => by
      cases ht
  | _, x :: xs, t, h, ht => by
      rw [List.mem_cons] at ht
      cases ht with
      | inl htx =>
          rw [htx]
          exact h.head_le_top
      | inr htxs =>
          exact (solution h.tail htxs).trans h.head_le_top
end BKAR.OrderedSimplexParams
