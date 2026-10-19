-- Prove2me | solution 1 for BookProof.ChapterA.JY_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:25:45.982221+00:00
-- url     : https://prove2.me/submissions/e9711f62-bce6-447b-afbd-b6cdaaf77ad5

-- Generated from ChapterA1e.lean — solution of BookProof.ChapterA.JY_isClosed
import Mathlib
import Definitions.Def_ChapterA1e
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution {Y : Submodule ℝ V} (hY : IsClosed (Y : Set V)) :
    IsClosed ((JY Y : Submodule ℝ V) : Set V) := by

  -- Since `Jmap` is a linear isometry equivalence, it is a homeomorphism.
  have h_homeo : IsHomeomorph (Jmap : V → V) := by
    convert Homeomorph.isHomeomorph ( Jmap.toHomeomorph ) using 1
    · rfl
  convert h_homeo.isClosedMap Y hY using 1
  rfl
