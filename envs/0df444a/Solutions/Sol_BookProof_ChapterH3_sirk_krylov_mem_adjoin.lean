-- Prove2me | solution 1 for BookProof.ChapterH3.sirk_krylov_mem_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:34:44.898547+00:00
-- url     : https://prove2.me/submissions/249057f5-c037-4886-8c3f-c8f7891405be

-- Generated from ChapterH3.lean — solution of BookProof.ChapterH3.sirk_krylov_mem_adjoin
import Mathlib
import Definitions.Def_ChapterH3
open BookProof.ChapterH3



open scoped BigOperators
open intervalIntegral


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution
    (Xm : Module.End ℂ E) (Y X : ℕ → Module.End ℂ E)
    (hX : ∀ j, X j = Y j * Xm) (v : E) (j : ℕ) :
    ∃ r ∈ Algebra.adjoin ℂ ({Xm} ∪ Set.range Y),
      sirkKrylov X v j = r v := by

  induction j with
  | zero => exact ⟨1, OneMemClass.one_mem _, by simp [sirkKrylov]⟩
  | succ j ih =>
    obtain ⟨r, hr, hr'⟩ := ih
    refine ⟨X (j + 1) * r, ?_, ?_⟩
    · refine Subalgebra.mul_mem _ ?_ hr
      rw [hX]
      exact Subalgebra.mul_mem _
        (Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_range_self _)))
        (Algebra.subset_adjoin (Set.mem_union_left _ rfl))
    · simp [sirkKrylov, hr']
