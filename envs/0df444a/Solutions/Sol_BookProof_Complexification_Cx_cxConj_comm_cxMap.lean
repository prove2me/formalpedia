-- Prove2me | solution 1 for BookProof.Complexification.Cx.cxConj_comm_cxMap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:18:10.352321+00:00
-- url     : https://prove2.me/submissions/14e89130-070c-4153-808f-e2a76a6417d0

-- Generated from Complexification.lean — solution of BookProof.Complexification.Cx.cxConj_comm_cxMap
import Mathlib
import Definitions.Def_Complexification
import Definitions.Def_ChapterQgOuterFockCoreFL
open BookProof.Complexification
open BookProof.Complexification.Cx



open scoped RealInnerProductSpace
open RCLike


set_option linter.unusedSectionVars false

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

set_option maxHeartbeats 1000000 in
theorem solution (m : W →L[ℝ] W) (x : Cx W) :
    cxConj (cxMap m x) = cxMap m (cxConj x) := by

  ext <;> simp
