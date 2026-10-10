-- Prove2me | solution 1 for BookProof.ChapterLayerNorm.scoreSoftmax_layerNorm_ge
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T06:21:10.317069+00:00
-- url     : https://prove2.me/submissions/a3808831-0cee-4a8b-a860-44e01d012134
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterLayerNorm.lean — solution of BookProof.ChapterLayerNorm.scoreSoftmax_layerNorm_ge
import Mathlib
import Definitions.Def_ChapterLayerNorm
import Theorems.Thm_BookProof_ChapterLayerNorm_abs_inner_layerNorm_le
import Theorems.Thm_BookProof_ChapterAttentionRetrieval_scoreSoftmax_ge_of_spread
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterTotalVariance
open BookProof.ChapterLayerNorm



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterSoftmaxSharpness
open ChapterTotalVariance

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {m : ℕ} {beta : ℝ} (hb : 0 ≤ beta) (hd : 0 < d)
    {q : Fin d → ℝ} {k : Fin m → (Fin d → ℝ)} (hq : 0 < BookProof.ChapterLayerNorm.variance q)
    (hk : ∀ j, 0 < BookProof.ChapterLayerNorm.variance (k j)) (j : Fin m) :
    Real.exp (-(beta * (2 * d))) / (m : ℝ)
      ≤ scoreSoftmax beta (fun l => ∑ i, layerNorm q i * layerNorm (k l) i) j := by

  refine BookProof.ChapterAttentionRetrieval.scoreSoftmax_ge_of_spread hb _ j fun l => ?_
  have h1 := abs_inner_layerNorm_le hd hq (hk l)
  have h2 := abs_inner_layerNorm_le hd hq (hk j)
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  linarith [h1'.2, h2'.1]
