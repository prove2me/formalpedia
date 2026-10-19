-- Prove2me | solution 1 for BookProof.QgOuterFockFullFL.qgSectorExt_core
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:30:48.22164+00:00
-- url     : https://prove2.me/submissions/e303cd63-2a11-4320-88f4-3c6980a3cdf0

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterSqSumFarisLavine
import Mathlib
import Definitions.Def_ChapterQgOuterFockFullFL
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
-- Generated from ChapterQgOuterFockFullFL.lean — theorem BookProof.QgOuterFockFullFL.qgSectorExt_core
open BookProof.HermiteProductCore
open BookProof.QgOuterFock
open BookProof.QgOuterFockFL
open BookProof.QgOuterFockFullFL



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.Qg3DGaugeEsa BookProof.QuantumGravity3DGauge
open BookProof.GaussCoreQuadBounds BookProof.SqSumFarisLavine
open Filter Topology

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
theorem h42_core_dense {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (d : CoreData F) : DenseRange (d.coreRange.subtypeL) := by
  rw [Metric.denseRange_iff]
  intro f ε hε
  obtain ⟨x, hx⟩ := d.C.surj f
  obtain ⟨y, hy0, hy1, hy2⟩ := d.gc.approx x (ε / 2) (by positivity)
  refine ⟨⟨d.coreShift ⟨(y : F), hy0⟩, ⟨_, rfl⟩⟩, ?_⟩
  simp only [Submodule.subtypeL_apply, CoreData.coreShift_apply]
  have hyy : (⟨(y : F), d.gc.le hy0⟩ : d.C.dom) = y := rfl
  rw [hyy, dist_eq_norm]
  calc ‖f - (d.C.op y + (y : F))‖ = ‖(d.C.op x - d.C.op y) + ((x : F) - (y : F))‖ := by
        rw [← hx]; congr 1; abel
    _ ≤ ‖d.C.op x - d.C.op y‖ + ‖(x : F) - (y : F)‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := by
        rw [norm_sub_rev (d.C.op x), norm_sub_rev (x : F)]; exact add_lt_add hy2 hy1
    _ = ε := by ring

theorem h42_ext_core {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (d : CoreData F) (p : d.C₀) (h : (p : F) ∈ d.C.dom) : d.ext ⟨(p : F), h⟩ = d.H₀ p := by
  have hs : shiftOp d.C ⟨(p : F), h⟩ = d.coreRange.subtypeL (d.coreEquiv p) := rfl
  simp only [CoreData.ext, LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  rw [hs, CoreData.extCLM, ContinuousLinearMap.extend_eq _ (h42_core_dense d)
    (isUniformEmbedding_subtype_val.isUniformInducing)]
  simp [CoreData.resolvedCLM, CoreData.resolvedMap]

theorem solution (n : ℕ) (p : polyGaussCore (d := n * 84))
    (h : (p : L2d (n * 84)) ∈ (harmFried (n * 84)).dom) :
    qgSectorExt n ⟨(p : L2d (n * 84)), h⟩ = qgSectorHam n p := by
  exact h42_ext_core (qgSectorData n) p h

