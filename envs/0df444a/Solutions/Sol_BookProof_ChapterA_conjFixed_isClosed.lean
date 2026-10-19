-- Prove2me | solution 1 for BookProof.ChapterA.conjFixed_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:43:38.361126+00:00
-- url     : https://prove2.me/submissions/ce357f43-3444-45a6-a5ce-fb4a76efef4e

-- Generated from ChapterA1f.lean — solution of BookProof.ChapterA.conjFixed_isClosed
import Mathlib
import Definitions.Def_ChapterA1f
import Definitions.Def_ChapterA1
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (θ : AntiUnitary V) :
    IsClosed ((conjFixed θ : Submodule ℝ V) : Set V) := by

  have h : ((conjFixed θ : Submodule ℝ V) : Set V) = {v | θ v = v} := rfl
  rw [h]; exact isClosed_eq θ.continuous continuous_id
