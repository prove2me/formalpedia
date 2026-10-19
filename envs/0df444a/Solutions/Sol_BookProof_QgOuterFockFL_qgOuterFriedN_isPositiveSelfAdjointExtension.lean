-- Prove2me | solution 1 for BookProof.QgOuterFockFL.qgOuterFriedN_isPositiveSelfAdjointExtension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:40:33.562622+00:00
-- url     : https://prove2.me/submissions/dccda700-5ac0-481d-a78d-9269d91ce0fe

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterYangMillsFriedrichs
import Theorems.Thm_BookProof_QgOuterFockFL_Comparison_isPositiveSelfAdjointExtension
import Theorems.Thm_BookProof_QgOuterFockFL_harmFried_op_core
import Theorems.Thm_BookProof_QgOuterFockFL_qgOuterFriedN_apply
import Theorems.Thm_BookProof_QgOuterFockFL_qgOuterCore_le_friedDom
-- Generated from ChapterQgOuterFockFarisLavine.lean — theorem BookProof.QgOuterFockFL.qgOuterFriedN_isPositiveSelfAdjointExtension
open BookProof.DirectSumEsa
open BookProof.HermiteProductCore
open BookProof.QgHermiteOscillator
open BookProof.QgOuterFock
open BookProof.YangMillsFriedrichs
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
theorem h44_harmW_eq (d : ℕ) : BookProof.QgOuterFockFL.harmW (d := d) = BookProof.QgHermiteOscillator.harmW := by
  funext x; rfl
theorem h44_harmCore_eq (d : ℕ) :
    BookProof.QgOuterFockFL.harmCore (d := d) = BookProof.QgHermiteOscillator.harmCore := by
  unfold BookProof.QgOuterFockFL.harmCore BookProof.QgHermiteOscillator.harmCore
  congr 1

theorem solution :
    IsPositiveSelfAdjointExtension qgOuterN qgOuterFriedN := by
  refine BookProof.QgOuterFockFL.Comparison.isPositiveSelfAdjointExtension qgOuterComparison _
    (fun x => ⟨BookProof.QgOuterFockFL.qgOuterCore_le_friedDom x.2, ?_⟩)
  apply lp.ext
  funext n
  have := BookProof.QgOuterFockFL.qgOuterFriedN_apply
    ⟨(x : BookProof.QgOuterFockFL.qgOuterFock), BookProof.QgOuterFockFL.qgOuterCore_le_friedDom x.2⟩ n
  refine this.trans ?_
  refine (BookProof.QgOuterFockFL.harmFried_op_core (n * 84)
    ⟨((x : BookProof.QgOuterFockFL.qgOuterFock) : ∀ n : ℕ, L2d (n * 84)) n, x.2.2 n⟩ _).trans ?_
  refine (LinearMap.congr_fun (h44_harmCore_eq (n * 84)) _).trans ?_
  simp only [BookProof.QgOuterFock.qgOuterN, BookProof.DirectSumEsa.dsOp]
  rfl

