-- Prove2me | solution 1 for BookProof.RelationShiftInvert.unitaryU_mem_relDomain
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:27:37.230146+00:00
-- url     : https://prove2.me/submissions/fd394a9b-c613-4a0b-84e9-c6f6621fe95a

import Definitions.Def_ChapterNonnegUnitaryGroup
import Definitions.Def_ChapterRelationShiftInvert

open BookProof.PositiveSquareRoot
open BookProof.NonnegUnitaryGroup
open BookProof.RelationShiftInvert

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {T T₁ T₂ : Submodule ℂ (F × F)}

theorem solution (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) (x : relDomain T) (t : ℝ) :
    unitaryU hT hsv t (x : F) ∈ relDomain T := by
  obtain ⟨k, hk⟩ := mem_relDomain_iff.1 x.2
  exact mem_relDomain_iff.2 ⟨unitaryU hT hsv t k, mem_unitaryU hT hsv hk t⟩
