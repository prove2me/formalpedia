-- Prove2me | solution 1 for BookProof.ChapterA.JY_isSubsystem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:25:47.156429+00:00
-- url     : https://prove2.me/submissions/9de847f7-26f3-4c0a-b695-caf337702610

-- Generated from ChapterA1e.lean — solution of BookProof.ChapterA.JY_isSubsystem
import Mathlib
import Definitions.Def_ChapterA1e
import Theorems.Thm_BookProof_ChapterA_Jmap_mem_JY
import Theorems.Thm_BookProof_ChapterA_JY_isClosed
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (M : System ℂ V) {Y : Submodule ℝ V}
    (hY : (rxSystem M).IsSubsystem Y) : (rxSystem M).IsSubsystem (JY Y) := by

  refine ⟨ JY_isClosed hY.1, ?_ ⟩;
  intro m hm w hw;
  obtain ⟨ y, hy, rfl ⟩ := hw;
  convert Jmap_mem_JY ( hY.2 _ hm _ hy ) using 1;
  obtain ⟨ m', hm', rfl ⟩ := hm;
  simp [ rxMap, Jmap ]
