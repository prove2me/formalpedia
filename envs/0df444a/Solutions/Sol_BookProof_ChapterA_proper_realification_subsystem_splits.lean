-- Prove2me | solution 1 for BookProof.ChapterA.proper_realification_subsystem_splits
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:26:34.364314+00:00
-- url     : https://prove2.me/submissions/ea085c90-aee7-4c80-86e7-731f578a9974

-- Generated from ChapterA1e.lean — solution of BookProof.ChapterA.proper_realification_subsystem_splits
import Mathlib
import Definitions.Def_ChapterA1e
import Theorems.Thm_BookProof_ChapterA_realification_splits
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (M : System ℂ V) (h : M.IsIrreducible)
    {Y : Submodule ℝ V} (hY : (rxSystem M).IsSubsystem Y) (hbot : Y ≠ ⊥) (htop : Y ≠ ⊤) :
    Y ⊓ JY Y = ⊥ ∧ (Y ⊔ JY Y).topologicalClosure = ⊤ := by

  rcases realification_splits M h Y hY with h₁ | h₁ | h₁
  · exact absurd h₁ hbot
  · exact absurd h₁ htop
  · exact h₁
