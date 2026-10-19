-- Prove2me | solution 1 for BookProof.ChapterA.Jmap_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:23:35.103116+00:00
-- url     : https://prove2.me/submissions/13172001-f4df-4e67-b235-19c728c8938c

-- Generated from ChapterA1d.lean — solution of BookProof.ChapterA.Jmap_sq
import Mathlib
import Definitions.Def_ChapterA1d
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace




attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

set_option maxHeartbeats 1000000 in
theorem solution (x : V) : Jmap (Jmap x) = -x := by

  change (Complex.I : ℂ) • ((Complex.I : ℂ) • x) = -x
  rw [smul_smul]; simp
