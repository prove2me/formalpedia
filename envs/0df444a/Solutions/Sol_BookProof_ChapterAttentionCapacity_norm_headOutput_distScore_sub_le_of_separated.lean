-- Prove2me | solution 1 for BookProof.ChapterAttentionCapacity.norm_headOutput_distScore_sub_le_of_separated
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T16:38:18.742233+00:00
-- url     : https://prove2.me/submissions/6d119470-06ed-4231-8a6b-e9243629980e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterAttentionCapacity.lean — solution of BookProof.ChapterAttentionCapacity.norm_headOutput_distScore_sub_le_of_separated
import Mathlib
import Definitions.Def_ChapterAttentionCapacity
import Theorems.Thm_BookProof_ChapterAttentionCapacity_distScore_margin_of_separated
import Theorems.Thm_BookProof_ChapterAttentionRetrieval_norm_headOutput_sub_le_of_margin
import Definitions.Def_ChapterAttentionOutput
import Theorems.Thm_BookProof_ChapterAttentionRetrieval_norm_headOutput_sub_le_of_margin
open BookProof.ChapterAttentionRetrieval
open BookProof.ChapterAttentionOutput
open BookProof.ChapterAttentionCapacity



open scoped BigOperators

open Filter Topology

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution
    {k : Fin m → EuclideanSpace ℝ (Fin n)} {v : Fin m → E} {r beta C : ℝ}
    (hb : 0 ≤ beta) (hr : 0 ≤ r) (hsep : keysSeparated k r) (hv : ∀ l, ‖v l‖ ≤ C)
    (i : Fin m) :
    ‖headOutput beta (distScore (k i) k) v - v i‖
      ≤ 2 * C * (((m : ℝ) - 1) * Real.exp (-(beta * r ^ 2))) := norm_headOutput_sub_le_of_margin hb _ v i (distScore_margin_of_separated hr hsep i) hv
