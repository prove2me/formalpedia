-- Prove2me | solution 1 for BookProof.QgOuterFockFL.qgOuterFriedN_apply
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:41:03.162968+00:00
-- url     : https://prove2.me/submissions/8c91aafc-7d1f-4454-b1a4-836148dbbf86

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Mathlib
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockEsa
-- Generated from ChapterQgOuterFockFarisLavine.lean — theorem BookProof.QgOuterFockFL.qgOuterFriedN_apply
open BookProof.HermiteProductCore
open BookProof.QgOuterFock
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


theorem solution (x : qgOuterFriedDom) (n : ℕ) :
    ((qgOuterFriedN x : BookProof.QgOuterFockFL.qgOuterFock) : ∀ n : ℕ, L2d (n * 84)) n
      = (harmFried (n * 84)).op ⟨((x : BookProof.QgOuterFockFL.qgOuterFock) : ∀ n : ℕ, L2d (n * 84)) n, x.2.1 n⟩ := by
  exact dsCompOp_fib (fun n : ℕ => harmFried (n * 84)) x n

