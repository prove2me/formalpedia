-- Prove2me | solution 1 for BookProof.RelationShiftInvert.hasDerivAt_unitaryU_relOp
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:31:49.671135+00:00
-- url     : https://prove2.me/submissions/9499f324-c7ed-48f0-9415-dfb7c625f5b6

import Definitions.Def_ChapterRelationShiftInvert

open BookProof.PositiveSquareRoot
open BookProof.HashimotoShiftInvert
open BookProof.NonnegUnitaryGroup
open BookProof.RelationShiftInvert

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {T T₁ T₂ : Submodule ℂ (F × F)}

theorem solution (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) (x : relDomain T) (t : ℝ) :
    HasDerivAt (fun s : ℝ => unitaryU hT hsv s (x : F))
      ((-Complex.I) • unitaryU hT hsv t (relOp hsv x)) t := by
  exact BookProof.NonnegUnitaryGroup.hasDerivAt_unitaryU hT hsv (relOpFun_mem x) t
