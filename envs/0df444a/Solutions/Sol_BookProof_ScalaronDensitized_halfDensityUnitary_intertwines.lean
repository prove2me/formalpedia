-- Prove2me | solution 1 for BookProof.ScalaronDensitized.halfDensityUnitary_intertwines
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T17:50:20.189058+00:00
-- url     : https://prove2.me/submissions/5e04df7e-90ca-4b38-bae5-19fdc79594d8

-- Generated from ChapterScalaronDensitizedTransfer.lean — theorem BookProof.ScalaronDensitized.halfDensityUnitary_intertwines
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Mathlib
import Definitions.Def_ChapterScalaronDensitizedTransfer
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Definitions.Def_ChapterStarobinskyPotential
import Theorems.Thm_BookProof_ScalaronDensitized_halfDensityUnitary_mem_densConfCore
open BookProof.ChapterLinftyMultiplication
open BookProof.NavierStokesFlow.FockContinuum
open BookProof.QuantumGravityHalfDensity
open BookProof.Starobinsky
open BookProof.ScalaronDensitized



open MeasureTheory Set Filter Topology
open BookProof.Starobinsky BookProof.QuantumGravityDensitized
open BookProof.QuantumGravityHalfDensity
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockContinuum
open BookProof.FarisLavine BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable (M alpha : ℝ)
open BookProof.ScalaronDensitized in
theorem solution (x : physConfCore M alpha) :
    ((densConfOp M alpha ⟨halfDensityUnitary (x : Lp ℂ 2 physMeasure),
        halfDensityUnitary_mem_densConfCore M alpha x⟩ : densConfCore M alpha) :
          Lp ℂ 2 qgSrcMeasure)
      = halfDensityUnitary ((physConfOp M alpha x : physConfCore M alpha) :
          Lp ℂ 2 physMeasure) := by
  refine Lp.ext ?_
  have hL : (((densConfOp M alpha ⟨halfDensityUnitary (x : Lp ℂ 2 physMeasure),
        halfDensityUnitary_mem_densConfCore M alpha x⟩ : densConfCore M alpha) :
          Lp ℂ 2 qgSrcMeasure) : ℝ → ℂ)
      =ᵐ[qgSrcMeasure] fun y => (densConfV M alpha y : ℂ) *
        ((halfDensityUnitary (x : Lp ℂ 2 physMeasure) : Lp ℂ 2 qgSrcMeasure) : ℝ → ℂ) y :=
    (memLp_mul (measurable_densConfV M alpha)
      (halfDensityUnitary_mem_densConfCore M alpha x)).coeFn_toLp
  have hU : ∀ g : Lp ℂ 2 physMeasure, ((halfDensityUnitary g : Lp ℂ 2 qgSrcMeasure) : ℝ → ℂ)
      =ᵐ[qgSrcMeasure] fun y => (g : ℝ → ℂ) (qgSquare y) := fun g =>
    Lp.coeFn_compMeasurePreserving _ measurePreserving_qgSquare
  have hH : (((physConfOp M alpha x : physConfCore M alpha) : Lp ℂ 2 physMeasure) : ℝ → ℂ)
      =ᵐ[physMeasure] fun e => (confV M alpha e : ℂ) * ((x : Lp ℂ 2 physMeasure) : ℝ → ℂ) e :=
    (memLp_mul (measurable_confV M alpha) x.2).coeFn_toLp
  have hH' := hH.comp_tendsto measurePreserving_qgSquare.quasiMeasurePreserving.tendsto_ae
  filter_upwards [hL, hU (x : Lp ℂ 2 physMeasure),
    hU ((physConfOp M alpha x : physConfCore M alpha) : Lp ℂ 2 physMeasure), hH'] with y h1 h2 h3 h4
  rw [h1, h2, h3]
  simp only [Function.comp_apply] at h4
  rw [h4]
  rfl
