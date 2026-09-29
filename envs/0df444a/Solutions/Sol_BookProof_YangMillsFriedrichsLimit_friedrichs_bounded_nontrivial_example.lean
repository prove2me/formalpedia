-- Prove2me | solution 1 for BookProof.YangMillsFriedrichsLimit.friedrichs_bounded_nontrivial_example
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T13:00:37.959449+00:00
-- url     : https://prove2.me/submissions/be2e1b98-de73-4fa6-a54a-a7a77944077d

-- Generated from ChapterYangMillsFriedrichsLimit.lean — solution of BookProof.YangMillsFriedrichsLimit.friedrichs_bounded_nontrivial_example
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Theorems.Thm_BookProof_YangMillsFriedrichsLimit_friedrichs_of_bounded
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFarisLavine
open BookProof.YangMillsFriedrichsLimit









open BookProof.FarisLavine BookProof.YangMillsFriedrichs



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution [CompleteSpace F] (D : Submodule ℂ F)
    (hdense : Dense (D : Set F)) :
    ∃ A : F →L[ℂ] F, (∀ x : D, A (x : F) = D.subtype x) ∧
      IsPositiveSelfAdjointExtension (D.subtype) (topRestrict A) := by

  refine friedrichs_of_bounded (D.subtype) hdense (fun x y => rfl) (fun x => ?_) 1 (fun x => ?_)
  · simp only [quadForm, Submodule.subtype_apply]
    simpa using inner_self_nonneg (𝕜 := ℂ) (x := (x : F))
  · simp
