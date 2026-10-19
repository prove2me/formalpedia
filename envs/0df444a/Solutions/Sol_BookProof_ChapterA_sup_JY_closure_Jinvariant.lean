-- Prove2me | solution 1 for BookProof.ChapterA.sup_JY_closure_Jinvariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:26:05.286985+00:00
-- url     : https://prove2.me/submissions/55e87292-92bd-4438-b40d-90a5343ff0b3

-- Generated from ChapterA1e.lean — solution of BookProof.ChapterA.sup_JY_closure_Jinvariant
import Mathlib
import Definitions.Def_ChapterA1e
import Theorems.Thm_BookProof_ChapterA_sup_JY_Jinvariant
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (Y : Submodule ℝ V) :
    ∀ x ∈ (Y ⊔ JY Y).topologicalClosure, Jmap x ∈ (Y ⊔ JY Y).topologicalClosure := by

  intro x hx;
  -- Since $Jmap$ is continuous and $Y ⊔ JY Y$ is $J$-invariant, we have $Jmap x ∈ (Y ⊔ JY
  -- Y).topologicalClosure$.
  have hJmap_cont : Continuous (Jmap : V → V) := by
    exact Jmap.toContinuousLinearEquiv.continuous;
  have hJmap_invariant : ∀ x ∈ Y ⊔ JY Y, Jmap x ∈ Y ⊔ JY Y := sup_JY_Jinvariant Y
  exact mem_closure_image hJmap_cont.continuousAt hx |> fun h => closure_mono (
      Set.image_subset_iff.mpr hJmap_invariant ) h
