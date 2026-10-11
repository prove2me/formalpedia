-- Prove2me | solution 1 for BookProof.QgOuterFockFL.polyGaussCore_le_harmFriedDom
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:38:13.888438+00:00
-- url     : https://prove2.me/submissions/25fa9a22-0c76-4ae1-b576-d2d95dd40074
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterQgOuterFockFarisLavine.lean — solution of BookProof.QgOuterFockFL.polyGaussCore_le_harmFriedDom
import Mathlib
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Theorems.Thm_BookProof_QgOuterFockFL_friedrichsComparison_extends
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterHermiteProductCore
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
variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]
variable (C : ∀ i, Comparison (G i))
variable (H : ∀ i, (C i).dom →ₗ[ℂ] G i)
variable {C H}

set_option maxHeartbeats 1000000 in
theorem solution (d : ℕ) :
    (polyGaussCore (d := d)) ≤ (harmFried d).dom :=
  fun v hv =>
    (friedrichsComparison_extends (harmPosSym d) polyGaussCore_dense ⟨v, hv⟩).choose
