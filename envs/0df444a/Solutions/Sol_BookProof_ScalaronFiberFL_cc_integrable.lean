-- Prove2me | solution 1 for BookProof.ScalaronFiberFL.cc_integrable
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-22T18:18:07.937361+00:00
-- url     : https://prove2.me/submissions/fed049aa-f9ac-484a-9e3c-6867ad1f6bc9

-- Generated from ChapterScalaronFiberFL.lean — solution of BookProof.ScalaronFiberFL.cc_integrable
import Mathlib
import Definitions.Def_ChapterScalaronFiberFL
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
theorem solution (f : ccSchwartz ℝ) {W : ℝ → ℝ} (hW : Continuous W) :
    Integrable fun x => W x * ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 := by

  have hsq : Continuous fun x => ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 := by fun_prop
  have hsupp : HasCompactSupport fun x => ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 :=
    f.2.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
  exact ((hW.mul hsq)).integrable_of_hasCompactSupport hsupp.mul_left
