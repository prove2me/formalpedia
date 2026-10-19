-- Prove2me | solution 1 for BookProof.ChapterA.rImagCx_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:08:27.390725+00:00
-- url     : https://prove2.me/submissions/18dcac77-e2fe-47bd-9f0e-7e29afa1a467

-- Generated from ChapterA1h.lean — solution of BookProof.ChapterA.rImagCx_sq
import Mathlib
import Definitions.Def_ChapterA1h
import Definitions.Def_Complexification
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
import Definitions.Def_ChapterQgOuterFockCoreFL
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


open BookProof.Complexification
open BookProof.ChapterA.AntiUnitary
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

set_option maxHeartbeats 1000000 in
theorem solution {M : System ℝ W} {J : W ≃ₗᵢ[ℝ] W} (hJ : IsRImaginary M J) (x : Cx W) :
    rImagCx J (rImagCx J x) = -x := by

  ext <;> simp [rImagCx_apply, hJ.1]
