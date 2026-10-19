-- Prove2me | solution 1 for BookProof.ScalaronFiberFL.hamS_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-16T20:29:40.197146+00:00
-- url     : https://prove2.me/submissions/ddedec43-8a5c-4785-8dea-ab40958516ec

-- Generated from ChapterScalaronFiberFL.lean — solution of BookProof.ScalaronFiberFL.hamS_apply
import Mathlib
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterWallEsaSemibounded
import Definitions.Def_ChapterWallEsaBddBelow
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterSchrodingerCutoffEsa
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterLeafGaps
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
theorem solution (W : WallPot) (s : ℝ) (f : ccSchwartz ℝ) (x : ℝ) :
    hamS W s f x
      = -deriv (deriv ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x + (W.pot s x : ℂ) * (f : 𝓢(ℝ, ℂ)) x := by

  simp [hamS, kinOpR_apply]
