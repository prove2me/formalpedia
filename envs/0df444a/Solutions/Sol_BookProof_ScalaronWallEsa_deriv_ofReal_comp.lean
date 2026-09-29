-- Prove2me | solution 1 for BookProof.ScalaronWallEsa.deriv_ofReal_comp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-17T12:55:17.029839+00:00
-- url     : https://prove2.me/submissions/c2265659-8e9a-4d3d-902c-47d0dbdc277c

-- Generated from ChapterScalaronWallEsa.lean — solution of BookProof.ScalaronWallEsa.deriv_ofReal_comp
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
theorem solution {g : ℝ → ℝ} (hg : Differentiable ℝ g) :
    deriv (fun y => ((g y : ℝ) : ℂ)) = fun x => ((deriv g x : ℝ) : ℂ) := funext fun x => ((hg x).hasDerivAt.ofReal_comp).deriv
