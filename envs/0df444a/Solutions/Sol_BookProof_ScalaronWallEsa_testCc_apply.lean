-- Prove2me | solution 1 for BookProof.ScalaronWallEsa.testCc_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-17T12:56:55.66773+00:00
-- url     : https://prove2.me/submissions/d8654e3d-ba10-4eb5-b3b5-64be0839c9d6

-- Generated from ChapterScalaronWallEsa.lean — solution of BookProof.ScalaronWallEsa.testCc_apply
import Mathlib
import Definitions.Def_ChapterScalaronWallEsa
open BookProof.ScalaronWallEsa













open MeasureTheory SchwartzMap Set
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.Starobinsky BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent
open BookProof.WeakSecondDeriv

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {g : ℝ → ℝ} (hg : IsTestFun g) (x : ℝ) :
    ((testCc hg : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x = ((g x : ℝ) : ℂ) := rfl
