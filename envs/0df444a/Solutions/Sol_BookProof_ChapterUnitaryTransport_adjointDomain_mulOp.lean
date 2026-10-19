-- Prove2me | solution 1 for BookProof.ChapterUnitaryTransport.adjointDomain_mulOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:45:36.172813+00:00
-- url     : https://prove2.me/submissions/893a03e7-557d-40c8-83df-2dcf3b62394f

-- Generated from ChapterUnitaryTransport.lean — solution of BookProof.ChapterUnitaryTransport.adjointDomain_mulOp
import Mathlib
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterUnboundedPosition
open BookProof.ChapterUnitaryTransport



open scoped InnerProductSpace
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterF7
open BookProof.ChapterUnboundedPosition


variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

set_option maxHeartbeats 1000000 in

theorem solution (f : ℤ → ℝ) :
    adjointDomain (mulDomain f) (mulOp f) = BookProof.ChapterUnboundedPosition.adjointDomain f :=
  rfl
