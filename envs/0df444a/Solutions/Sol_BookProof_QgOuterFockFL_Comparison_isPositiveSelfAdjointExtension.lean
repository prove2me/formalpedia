-- Prove2me | solution 1 for BookProof.QgOuterFockFL.Comparison.isPositiveSelfAdjointExtension
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:37:34.016289+00:00
-- url     : https://prove2.me/submissions/1b97fb1e-4af9-4b9a-91d4-47b2a1961189

-- Generated from ChapterQgOuterFockFarisLavine.lean — solution of BookProof.QgOuterFockFL.Comparison.isPositiveSelfAdjointExtension
import Mathlib
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Theorems.Thm_BookProof_QgOuterFockFL_Comparison_selfAdjoint
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.QgOuterFockFL



open scoped ENNReal


open BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFock
open BookProof.YangMillsFriedrichs
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.HashimotoShiftInvert
open BookProof.QgHermiteOscillator
open BookProof.HermiteProductCore

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution (C : Comparison F) {D : Submodule ℂ F}
    (H : D →ₗ[ℂ] F) (hHD : ∀ x : D, ∃ h : (x : F) ∈ C.dom, C.op ⟨(x : F), h⟩ = H x) :
    IsPositiveSelfAdjointExtension H C.op := ⟨hHD, C.sym, C.pos, C.selfAdjoint⟩
