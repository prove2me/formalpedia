-- Prove2me | solution 1 for BookProof.ChapterAttentionEntropy.shannonEntropy_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T04:31:09.054673+00:00
-- url     : https://prove2.me/submissions/75e89cf9-2fff-4dea-951c-2539a2a58e63

import Mathlib
import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionEntropy

open BookProof.ChapterAttentionEntropy

theorem solution {m : ℕ} {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1) :
    0 ≤ shannonEntropy p := by
  unfold shannonEntropy
  -- H(p) = -∑ pⱼ log pⱼ; each pⱼ log pⱼ ≤ 0 when 0 ≤ pⱼ ≤ 1
  refine neg_nonneg.mpr ?_
  refine Finset.sum_nonpos fun j _ => ?_
  have hlog : Real.log (p j) ≤ 0 := Real.log_nonpos (hp0 j) (hp1 j)
  exact mul_nonpos_of_nonneg_of_nonpos (hp0 j) hlog
