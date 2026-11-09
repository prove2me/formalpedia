-- Prove2me | solution 1 for BookProof.ScalaronFiberFL.integral_deriv_le_quadForm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:05:36.990989+00:00
-- url     : https://prove2.me/submissions/b496ec3d-9796-4f2f-9270-711909a03651

-- Generated from ChapterScalaronFiberFL.lean — solution of BookProof.ScalaronFiberFL.integral_deriv_le_quadForm
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
theorem solution (W : WallPot) (s : ℝ) (hs : 0 ≤ s) (f : ccSchwartz ℝ) :
    (∫ x, ‖deriv ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ ^ 2) ≤ quadForm (W.ham s) (ccEquiv ℝ f) := by

  rw [ham_quadForm]
  have h2 : (0 : ℝ) ≤ ∫ x, W.pot s x * ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 :=
    integral_nonneg fun x => mul_nonneg (W.pot_nonneg s hs x) (by positivity)
  linarith
