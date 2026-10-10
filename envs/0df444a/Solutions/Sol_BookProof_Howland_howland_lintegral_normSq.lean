-- Prove2me | solution 1 for BookProof.Howland.howland_lintegral_normSq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:11:15.059572+00:00
-- url     : https://prove2.me/submissions/dfbe0c63-001d-4fda-981f-dc233b9bb771

-- Generated from ChapterHowlandAutonomization.lean — solution of BookProof.Howland.howland_lintegral_normSq
import Mathlib
import Definitions.Def_ChapterHowlandAutonomization
open BookProof.Howland




open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [NormedAddCommGroup H]
variable {U : ℝ → ℝ → H → H}

set_option maxHeartbeats 1000000 in
theorem solution (hU : IsPropagator U) (σ : ℝ) (ψ : ℝ → H) :
    ∫⁻ t, ENNReal.ofReal (‖howland U σ ψ t‖ ^ 2)
      = ∫⁻ t, ENNReal.ofReal (‖ψ t‖ ^ 2) := by

  have hpt : ∀ t : ℝ, ENNReal.ofReal (‖howland U σ ψ t‖ ^ 2)
      = ENNReal.ofReal (‖ψ (t - σ)‖ ^ 2) := by
    intro t
    simp [howland, hU.isometry]
  calc ∫⁻ t, ENNReal.ofReal (‖howland U σ ψ t‖ ^ 2)
      = ∫⁻ t, ENNReal.ofReal (‖ψ (t + -σ)‖ ^ 2) := by
        refine lintegral_congr fun t => ?_
        rw [hpt t]
        ring_nf
    _ = ∫⁻ t, ENNReal.ofReal (‖ψ t‖ ^ 2) :=
        lintegral_add_right_eq_self (fun t => ENNReal.ofReal (‖ψ t‖ ^ 2)) (-σ)
