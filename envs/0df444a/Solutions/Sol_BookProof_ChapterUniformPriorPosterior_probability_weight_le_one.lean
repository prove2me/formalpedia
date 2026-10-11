-- Prove2me | solution 1 for BookProof.ChapterUniformPriorPosterior.probability_weight_le_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:14:08.220717+00:00
-- url     : https://prove2.me/submissions/189f5299-6b34-49fa-9702-395d579d86f9

-- Generated from ChapterUniformPriorPosterior.lean — solution of BookProof.ChapterUniformPriorPosterior.probability_weight_le_one
import Mathlib
import Definitions.Def_ChapterUniformPriorPosterior
open BookProof.ChapterUniformPriorPosterior



open scoped BigOperators


variable {Hyp : Type*} [Fintype Hyp] [DecidableEq Hyp]

variable {Hyp : Type*} [Fintype Hyp] [DecidableEq Hyp]

set_option maxHeartbeats 1000000 in
theorem solution (q : Hyp → ℝ) (hq_nonneg : ∀ x, 0 ≤ q x)
    (hq_sum : ∑ x, q x = 1) (x : Hyp) : q x ≤ 1 := by

  exact hq_sum ▸ Finset.single_le_sum (fun y _ => hq_nonneg y) (Finset.mem_univ x)
