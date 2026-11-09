-- Prove2me | solution 1 for BookProof.ScalaronFiberFL.xCc_eq_toLp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:05:58.587722+00:00
-- url     : https://prove2.me/submissions/7f80ae3f-bc2b-48d2-b8ba-376c225d7d42

-- Generated from ChapterScalaronFiberFL.lean — solution of BookProof.ScalaronFiberFL.xCc_eq_toLp
import Mathlib
import Definitions.Def_ChapterScalaronFiberFL
import Theorems.Thm_BookProof_ScalaronEsa_opCc_apply
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
    xCc (ccEquiv ℝ f) = (mulCc (fun x : ℝ => x) contDiff_id f).toLp 2 (volume : Measure ℝ) := opCc_apply _ _ _
