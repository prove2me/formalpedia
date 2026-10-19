-- Prove2me | solution 1 for BookProof.QgOuterFockFL.qgOuterCore_le_friedDom
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:41:10.737611+00:00
-- url     : https://prove2.me/submissions/3cef61b7-3b8d-43ac-8441-dc8df5b91d8b

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Theorems.Thm_BookProof_QgOuterFockFL_polyGaussCore_le_harmFriedDom
-- Generated from ChapterQgOuterFockFarisLavine.lean — theorem BookProof.QgOuterFockFL.qgOuterCore_le_friedDom
open BookProof.DirectSumEsa
open BookProof.HermiteProductCore
open BookProof.QgHermiteOscillator
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
theorem h42_core_le : qgOuterCore ≤ qgOuterFriedDom := by
  intro x hx
  refine ⟨fun n => BookProof.QgOuterFockFL.polyGaussCore_le_harmFriedDom _ (hx.2 n),
    BookProof.DirectSumEsa.memLp_of_finite_support (hx.1.subset ?_)⟩
  intro n hn
  simp only [Set.mem_setOf_eq] at hn ⊢
  intro h0
  apply hn
  rw [h0, opTot_of_mem _ (Submodule.zero_mem _)]
  exact map_zero _

theorem solution : qgOuterCore ≤ qgOuterFriedDom := by
  exact h42_core_le

