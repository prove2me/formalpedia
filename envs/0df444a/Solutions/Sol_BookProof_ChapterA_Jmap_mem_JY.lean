-- Prove2me | solution 1 for BookProof.ChapterA.Jmap_mem_JY
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:25:29.194782+00:00
-- url     : https://prove2.me/submissions/94c89d88-c265-4d99-853c-8fb3a04bc47c

-- Generated from ChapterA1e.lean — solution of BookProof.ChapterA.Jmap_mem_JY
import Mathlib
import Definitions.Def_ChapterA1e
import Theorems.Thm_BookProof_ChapterA_mem_JY
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution {Y : Submodule ℝ V} {y : V} (hy : y ∈ Y) : Jmap y ∈ JY Y := mem_JY.2 ⟨y, hy, rfl⟩
