-- Prove2me | solution 1 for BookProof.ChapterA.mem_JY
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:25:27.917628+00:00
-- url     : https://prove2.me/submissions/05406879-b143-4871-86f8-e081da58e932

-- Generated from ChapterA1e.lean — solution of BookProof.ChapterA.mem_JY
import Mathlib
import Definitions.Def_ChapterA1e
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution {Y : Submodule ℝ V} {x : V} : x ∈ JY Y ↔ ∃ y ∈ Y, Jmap y = x := by

  simp [JY, Submodule.mem_map]
