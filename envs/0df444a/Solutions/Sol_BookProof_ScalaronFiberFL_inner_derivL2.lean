-- Prove2me | solution 1 for BookProof.ScalaronFiberFL.inner_derivL2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T06:42:35.994448+00:00
-- url     : https://prove2.me/submissions/8a761438-5fa0-4faf-91c0-bf985136baca

import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterWallEsaSemibounded
import Definitions.Def_ChapterWallEsaBddBelow
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterSchrodingerCutoffEsa
import Definitions.Def_ChapterFriedrichsExtension
import Mathlib
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterQgOuterFockFlow
-- Generated from ChapterScalaronFiberFL.lean — theorem BookProof.ScalaronFiberFL.inner_derivL2
open BookProof.ScalaronEsa
open BookProof.ScalaronFiberFL



open MeasureTheory SchwartzMap
open BookProof.StrichartzWave
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallEsaSemibounded BookProof.WallEsaBddBelow
open BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.SchrodingerCutoff BookProof.FriedrichsExtension

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (W : WallPot) (s : ℝ)
theorem solution (f g : ccSchwartz ℝ) :
    (inner ℂ ((ccEquiv ℝ f : ccDomain ℝ) : L2R) (derivL2 g) : ℂ)
      = ∫ y : ℝ, (starRingEnd ℂ) ((f : 𝓢(ℝ, ℂ)) y)
          * deriv ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) y := by
  change inner ℂ ((f : 𝓢(ℝ, ℂ)).toLp 2 (volume : Measure ℝ))
    ((SchwartzMap.derivCLM ℂ ℂ (g : 𝓢(ℝ, ℂ))).toLp 2 (volume : Measure ℝ)) = _
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [SchwartzMap.coeFn_toLp (f : 𝓢(ℝ, ℂ)) 2 volume,
    SchwartzMap.coeFn_toLp (SchwartzMap.derivCLM ℂ ℂ (g : 𝓢(ℝ, ℂ))) 2 volume] with x hx1 hx2
  rw [hx1, hx2, SchwartzMap.derivCLM_apply]
  simp [mul_comm]
