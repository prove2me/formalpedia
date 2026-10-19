-- Prove2me | solution 1 for BookProof.ChapterSchurIrreducible.isClosed_rangeClosure
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:25:59.297152+00:00
-- url     : https://prove2.me/submissions/caa02b88-3c2d-411e-b8fe-f12b92e16b0c

-- Generated from ChapterSchurIrreducible.lean — solution of BookProof.ChapterSchurIrreducible.isClosed_rangeClosure
import Mathlib
import Definitions.Def_ChapterSchurIrreducible
import Definitions.Def_ChapterA
open BookProof.ChapterSchurIrreducible



open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA.System

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (F : V →L[ℂ] V) :
    IsClosed ((rangeClosure F : Submodule ℂ V) : Set V) := Submodule.isClosed_topologicalClosure _
