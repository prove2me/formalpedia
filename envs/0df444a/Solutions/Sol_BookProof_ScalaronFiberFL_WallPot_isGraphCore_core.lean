-- Prove2me | solution 1 for BookProof.ScalaronFiberFL.WallPot.isGraphCore_core
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-03T04:44:02.10854+00:00
-- url     : https://prove2.me/submissions/259651f8-cda2-4c06-a681-489754d65ef2

-- Generated from ChapterScalaronFiberFL.lean — solution of BookProof.ScalaronFiberFL.WallPot.isGraphCore_core
import Mathlib
import Definitions.Def_ChapterScalaronFiberFL
import Theorems.Thm_BookProof_ScalaronFiberFL_isGraphCore_of_esa
import Theorems.Thm_BookProof_ScalaronFiberFL_WallPot_ham_esa
import Theorems.Thm_BookProof_ScalaronFiberFL_WallPot_core_le_dom
import Theorems.Thm_BookProof_ScalaronFiberFL_WallPot_comparison_core
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
variable (W : WallPot) (s : ℝ) (hs : 0 ≤ s)

set_option maxHeartbeats 1000000 in
theorem solution : IsGraphCore (W.comparison s hs) (ccDomain ℝ) :=
  isGraphCore_of_esa (W.comparison s hs) (ccDomain ℝ) (W.core_le_dom s hs) (W.ham s)
      (fun p => W.comparison_core s hs p (W.core_le_dom s hs p.2)) (W.ham_esa s hs)
