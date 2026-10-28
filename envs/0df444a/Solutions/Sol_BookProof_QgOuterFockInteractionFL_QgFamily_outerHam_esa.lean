-- Prove2me | solution 1 for BookProof.QgOuterFockInteractionFL.QgFamily.outerHam_esa
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T05:33:14.603999+00:00
-- url     : https://prove2.me/submissions/04ae7951-4893-4917-8a22-63540ebfa600

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgOuterFockFullFL
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterSqSumFarisLavine
import Mathlib
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_gcSeq_tendsto
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_gcSeq_ext_tendsto
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_gcSeq_mem
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_ext_core
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_ext_essentiallySelfAdjointOn
import Theorems.Thm_BookProof_QgOuterFockInteractionFL_QgFamily_secHam_symmetricOn
import Theorems.Thm_BookProof_QgOuterFockInteractionFL_QgFamily_flc_nonneg
import Theorems.Thm_BookProof_QgOuterFockInteractionFL_QgFamily_secData_commForm_le
import Theorems.Thm_BookProof_DirectSumEsa_dsOp_essentiallySelfAdjointOn

import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockEsa
open BookProof.HermiteProductCore
open BookProof.QgOuterFock
open BookProof.QgOuterFockInteractionFL
open BookProof.QgOuterFockInteractionFL.QgFamily



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockFullFL
open BookProof.Qg3DGaugeEsa BookProof.QuantumGravity3DGauge
open BookProof.GaussCoreQuadBounds BookProof.SqSumFarisLavine

noncomputable section

variable (F : QgFamily)

open Filter Topology in
theorem qiOuter_core_defic {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] (d : CoreData G) (z : ℂ)
    (h : DeficiencyTrivialAt d.C.dom d.ext z) : DeficiencyTrivialAt d.C₀ d.H₀ z := by
  intro w hw
  apply h w
  intro x
  have hk : ∀ k : ℕ, (inner ℂ (d.ext (d.gcSeq x k)) w : ℂ)
      = z * inner ℂ ((d.gcSeq x k : d.C.dom) : G) w := by
    intro k
    have hc := BookProof.QgOuterFockCoreFL.CoreData.ext_core d
      ⟨((d.gcSeq x k : d.C.dom) : G), BookProof.QgOuterFockCoreFL.CoreData.gcSeq_mem d x k⟩
    have he : (⟨((d.gcSeq x k : d.C.dom) : G), d.gc.le
        (BookProof.QgOuterFockCoreFL.CoreData.gcSeq_mem d x k)⟩ : d.C.dom) = d.gcSeq x k :=
      Subtype.ext rfl
    rw [he] at hc
    rw [hc]
    exact hw _
  have t1 : Tendsto (fun k => (inner ℂ (d.ext (d.gcSeq x k)) w : ℂ)) atTop
      (𝓝 (inner ℂ (d.ext x) w)) :=
    (BookProof.QgOuterFockCoreFL.CoreData.gcSeq_ext_tendsto d x).inner tendsto_const_nhds
  have t2 : Tendsto (fun k => z * (inner ℂ ((d.gcSeq x k : d.C.dom) : G) w : ℂ)) atTop
      (𝓝 (z * inner ℂ (x : G) w)) :=
    ((BookProof.QgOuterFockCoreFL.CoreData.gcSeq_tendsto d x).inner tendsto_const_nhds).const_mul z
  simp only [hk] at t1
  exact tendsto_nhds_unique t1 t2

theorem solution (F : QgFamily) : EssentiallySelfAdjointOn qgOuterCore F.outerHam := by
  refine BookProof.DirectSumEsa.dsOp_essentiallySelfAdjointOn (fun n : ℕ => F.secHam n) ?_
  intro n
  have E := BookProof.QgOuterFockCoreFL.CoreData.ext_essentiallySelfAdjointOn (F.secData n)
    (F.secHam_symmetricOn n) F.flc_nonneg (F.secData_commForm_le n)
  exact ⟨qiOuter_core_defic (F.secData n) _ E.1, qiOuter_core_defic (F.secData n) _ E.2⟩
