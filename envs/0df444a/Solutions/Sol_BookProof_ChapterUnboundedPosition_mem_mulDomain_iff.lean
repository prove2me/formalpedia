-- Prove2me | solution 1 for BookProof.ChapterUnboundedPosition.mem_mulDomain_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:18:47.065406+00:00
-- url     : https://prove2.me/submissions/3ff006ba-0010-4fc4-92ea-ae2dba6ace08

import Mathlib
import Definitions.Def_ChapterUnboundedPosition
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterUnboundedPosition
open scoped ENNReal InnerProductSpace
open BookProof.ChapterContinuityUnitaryInfinite (L2Z)

theorem solution (f : ℤ → ℝ) (psi : L2Z) :
    psi ∈ mulDomain f ↔ Memℓp (fun k => (f k : ℂ) * (psi : ℤ → ℂ) k) 2 := by
  simp [mulDomain]
