-- Prove2me | solution 1 for BookProof.ChapterA.Jmap_mem_of_mem_JY
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:25:30.531578+00:00
-- url     : https://prove2.me/submissions/508cd22d-5312-4b66-a82e-a11838e37696

-- Generated from ChapterA1e.lean — solution of BookProof.ChapterA.Jmap_mem_of_mem_JY
import Mathlib
import Definitions.Def_ChapterA1e
import Theorems.Thm_BookProof_ChapterA_mem_JY
import Theorems.Thm_BookProof_ChapterA_Jmap_sq
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution {Y : Submodule ℝ V} {x : V} (hx : x ∈ JY Y) : Jmap x ∈ Y := by

  obtain ⟨y, hy, rfl⟩ := mem_JY.1 hx
  rw [Jmap_sq]
  exact Y.neg_mem hy
