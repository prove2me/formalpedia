-- Prove2me | solution 1 for BookProof.ScalaronFiberFL.inner_toLp_toLp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:05:33.222682+00:00
-- url     : https://prove2.me/submissions/2aa8f027-f20b-47dc-9311-0a7342e02f1b

-- Generated from ChapterScalaronFiberFL.lean — solution of BookProof.ScalaronFiberFL.inner_toLp_toLp
import Mathlib
import Definitions.Def_ChapterScalaronFiberFL
import Theorems.Thm_BookProof_StrichartzWave_inner_toLp_left
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

set_option maxHeartbeats 1000000 in
theorem solution (g h : 𝓢(ℝ, ℂ)) :
    (inner ℂ (g.toLp 2 (volume : Measure ℝ)) (h.toLp 2 (volume : Measure ℝ)) : ℂ)
      = ∫ x, (starRingEnd ℂ) (g x) * h x := by

  rw [inner_toLp_left]
  refine integral_congr_ae ?_
  filter_upwards [h.coeFn_toLp 2 (volume : Measure ℝ)] with x hx
  rw [hx]
