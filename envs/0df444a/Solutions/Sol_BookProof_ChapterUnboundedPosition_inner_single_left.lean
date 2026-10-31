-- Prove2me | solution 1 for BookProof.ChapterUnboundedPosition.inner_single_left
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T19:43:13.269679+00:00
-- url     : https://prove2.me/submissions/5a969002-fbb5-4631-9aef-1c6c03eb9cbd

import Mathlib
import Definitions.Def_ChapterUnboundedPosition
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterUnboundedPosition
open scoped ENNReal InnerProductSpace
open BookProof.ChapterContinuityUnitaryInfinite (L2Z)

theorem solution (phi : L2Z) (k : ℤ) (c : ℂ) :
    ⟪(lp.single 2 k c : L2Z), phi⟫_ℂ = (starRingEnd ℂ) c * (phi : ℤ → ℂ) k := by
  rw [lp.inner_single_left]
  simp [mul_comm]
