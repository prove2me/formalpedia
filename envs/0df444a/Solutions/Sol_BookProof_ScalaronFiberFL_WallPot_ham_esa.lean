-- Prove2me | solution 1 for BookProof.ScalaronFiberFL.WallPot.ham_esa
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-22T18:13:04.496566+00:00
-- url     : https://prove2.me/submissions/1e6cd895-2c4a-4ebd-a6d9-8c431bb9d9fd

-- Generated from ChapterScalaronFiberFL.lean — solution of BookProof.ScalaronFiberFL.WallPot.ham_esa
import Mathlib
import Definitions.Def_ChapterScalaronFiberFL
import Theorems.Thm_BookProof_ChapterDutchBook_Coherent_nonneg
import Theorems.Thm_BookProof_WallEsaBddBelow_oscillatorPlus_esa
open BookProof.ScalaronFiberFL
open BookProof.ScalaronFiberFL.WallPot




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
theorem solution (hs : 0 ≤ s) : EssentiallySelfAdjointOn (ccDomain ℝ) (W.ham s) :=
  oscillatorPlus_esa (fun x => W.V x + s) (W.smooth.add contDiff_const) (c := 0)
      (fun x => by simpa using add_nonneg (W.nonneg x) hs)
