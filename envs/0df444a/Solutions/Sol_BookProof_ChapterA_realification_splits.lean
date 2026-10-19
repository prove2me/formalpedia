-- Prove2me | solution 1 for BookProof.ChapterA.realification_splits
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:26:20.504916+00:00
-- url     : https://prove2.me/submissions/d0cadb7e-b05b-427a-b130-fdf2c5d7f982

-- Generated from ChapterA1e.lean — solution of BookProof.ChapterA.realification_splits
import Mathlib
import Definitions.Def_ChapterA1e
import Theorems.Thm_BookProof_ChapterA_inf_JY_Jinvariant
import Theorems.Thm_BookProof_ChapterA_inf_JY_isSubsystem
import Theorems.Thm_BookProof_ChapterA_sup_JY_closure_Jinvariant
import Theorems.Thm_BookProof_ChapterA_sup_JY_closure_isSubsystem
import Theorems.Thm_BookProof_ChapterA_complex_irreducible_iff_no_Jinvariant_subsystem
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (M : System ℂ V) (h : M.IsIrreducible)
    (Y : Submodule ℝ V) (hY : (rxSystem M).IsSubsystem Y) :
    Y = ⊥ ∨ Y = ⊤ ∨ (Y ⊓ JY Y = ⊥ ∧ (Y ⊔ JY Y).topologicalClosure = ⊤) := by

  have hcrit := (complex_irreducible_iff_no_Jinvariant_subsystem M).1 h
  obtain hsup | hsup :=
    hcrit (Y ⊔ JY Y).topologicalClosure (sup_JY_closure_isSubsystem M hY)
      (sup_JY_closure_Jinvariant Y)
  · refine Or.inl (le_bot_iff.mp ?_)
    exact le_trans le_sup_left (le_trans (Submodule.le_topologicalClosure _) hsup.le)
  · obtain hinf | hinf :=
      hcrit (Y ⊓ JY Y) (inf_JY_isSubsystem M hY) (inf_JY_Jinvariant Y)
    · exact Or.inr (Or.inr ⟨hinf, hsup⟩)
    · exact Or.inr (Or.inl (top_le_iff.mp (le_trans hinf.ge inf_le_left)))
