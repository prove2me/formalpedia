-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockContinuum.multOp_isSymmetricDom
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:28:54.590192+00:00
-- url     : https://prove2.me/submissions/a37c07c9-7398-4e77-a5f9-e2b362582377

import Mathlib
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
-- Generated from ChapterNavierStokesFockContinuum.lean — theorem BookProof.NavierStokesFlow.FockContinuum.multOp_isSymmetricDom
open BookProof.ChapterLinftyMultiplication
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa.NSFullData
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockContinuum


open MeasureTheory



open FullEsa

variable {X : Type*} [MeasurableSpace X]


theorem solution (μ : Measure X) {g : X → ℝ} (hg : Measurable g) :
    IsSymmetricDom (multOp μ hg) := by
  intro f h
  show (inner ℂ ((memLp_mul hg f.2).toLp _ : Lp ℂ 2 μ) (h : Lp ℂ 2 μ) : ℂ)
    = inner ℂ (f : Lp ℂ 2 μ) ((memLp_mul hg h.2).toLp _ : Lp ℂ 2 μ)
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_mul hg f.2).coeFn_toLp, (memLp_mul hg h.2).coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

