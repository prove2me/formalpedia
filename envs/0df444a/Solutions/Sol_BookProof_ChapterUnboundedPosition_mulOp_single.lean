-- Prove2me | solution 1 for BookProof.ChapterUnboundedPosition.mulOp_single
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-31T02:04:37.55489+00:00
-- url     : https://prove2.me/submissions/7563d79e-5cf4-4beb-be09-0b35165ee0c1

-- Generated from ChapterUnboundedPosition.lean — solution of BookProof.ChapterUnboundedPosition.mulOp_single
import Mathlib
import Definitions.Def_ChapterUnboundedPosition
import Theorems.Thm_BookProof_ChapterUnboundedPosition_single_mem_mulDomain
open BookProof.ChapterUnboundedPosition



open scoped ENNReal InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite (L2Z)

set_option maxHeartbeats 1000000 in
theorem solution (f : ℤ → ℝ) (n : ℤ) (c : ℂ) :
    mulOp f ⟨lp.single 2 n c, single_mem_mulDomain f n c⟩ = lp.single 2 n ((f n : ℂ) * c) := by
    ext k
    by_cases hk : k = n
    · subst hk
      simp [mulOp, lp.single_apply]
    · simp [mulOp, lp.single_apply, hk]
