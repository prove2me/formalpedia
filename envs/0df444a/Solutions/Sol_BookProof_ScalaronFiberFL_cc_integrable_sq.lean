-- Prove2me | solution 1 for BookProof.ScalaronFiberFL.cc_integrable_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-22T18:20:44.938819+00:00
-- url     : https://prove2.me/submissions/922854c9-5318-4d7a-bc94-6ee8e4f3c291

-- Generated from ChapterScalaronFiberFL.lean — solution of BookProof.ScalaronFiberFL.cc_integrable_sq
import Mathlib
import Definitions.Def_ChapterScalaronFiberFL
import Theorems.Thm_BookProof_ScalaronFiberFL_cc_integrable
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
theorem solution (f : ccSchwartz ℝ) :
    Integrable fun x => ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 := by

  simpa using cc_integrable f (W := fun _ => (1 : ℝ)) continuous_const
