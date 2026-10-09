-- Prove2me | solution 1 for BookProof.ChapterGravityPolymomentum.trace_vecMulVec
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T08:44:07.571982+00:00
-- url     : https://prove2.me/submissions/4851a1d0-4ad6-4cdd-ba94-570d2e365071

-- Generated from ChapterGravityPolymomentum.lean — solution of BookProof.ChapterGravityPolymomentum.trace_vecMulVec
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
open BookProof.ChapterGravityPolymomentum




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution (w u : Fin 4 → ℝ) :
    (vecMulVec w u).trace = ∑ a, w a * u a := by

  simp [Matrix.trace, vecMulVec_apply]
