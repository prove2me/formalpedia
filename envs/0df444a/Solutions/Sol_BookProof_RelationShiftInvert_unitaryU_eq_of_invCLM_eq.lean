-- Prove2me | solution 1 for BookProof.RelationShiftInvert.unitaryU_eq_of_invCLM_eq
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:37:16.3748+00:00
-- url     : https://prove2.me/submissions/df7fcbf7-4593-4dda-8158-31885a6c5de4

-- Generated from ChapterRelationShiftInvert.lean — theorem BookProof.RelationShiftInvert.unitaryU_eq_of_invCLM_eq
import Definitions.Def_ChapterPositiveSquareRootUnique
import Definitions.Def_ChapterNonnegSquareRoot
import Definitions.Def_ChapterNonnegResolvent
import Definitions.Def_ChapterNonnegUnitaryGroup
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterRelationShiftInvert



open BookProof.PositiveSquareRoot
open BookProof.HashimotoShiftInvert
open BookProof.NonnegUnitaryGroup

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {T T₁ T₂ : Submodule ℂ (F × F)}

theorem solution (hT₁ : IsNonnegSelfAdjoint T₁) (hT₂ : IsNonnegSelfAdjoint T₂)
    (hsv₁ : ∀ w : F, ((0 : F), w) ∈ T₁ → w = 0) (hsv₂ : ∀ w : F, ((0 : F), w) ∈ T₂ → w = 0)
    (heq : invCLM hT₁ = invCLM hT₂) (t : ℝ) :
    unitaryU hT₁ hsv₁ t = unitaryU hT₂ hsv₂ t := by
  have hrel : T₁ = T₂ := by
    ext p
    rcases p with ⟨x, y⟩
    constructor
    · intro hp
      have hx : invCLM hT₁ (x + y) = x := by
        apply invCLM_eq_of_mem hT₁
        simpa using hp
      have hm := invCLM_mem hT₂ (x + y)
      rw [← heq, hx] at hm
      simpa using hm
    · intro hp
      have hx : invCLM hT₂ (x + y) = x := by
        apply invCLM_eq_of_mem hT₂
        simpa using hp
      have hm := invCLM_mem hT₁ (x + y)
      rw [heq, hx] at hm
      simpa using hm
  subst T₂
  rfl
