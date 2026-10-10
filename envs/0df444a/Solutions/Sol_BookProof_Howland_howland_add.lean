-- Prove2me | solution 1 for BookProof.Howland.howland_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:11:03.808967+00:00
-- url     : https://prove2.me/submissions/c8bc45ab-3367-4e6a-9e92-eb775ee4b9f7

-- Generated from ChapterHowlandAutonomization.lean — solution of BookProof.Howland.howland_add
import Mathlib
import Definitions.Def_ChapterHowlandAutonomization
import Definitions.Def_ChapterMackeyImprimitivity
open BookProof.Howland




open MeasureTheory
open BookProof.ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [NormedAddCommGroup H]
variable {U : ℝ → ℝ → H → H}

set_option maxHeartbeats 1000000 in
theorem solution (hU : IsPropagator U) (σ τ : ℝ) (ψ : ℝ → H) :
    howland U σ (howland U τ ψ) = howland U (σ + τ) ψ := by

  funext t
  have hsub : t - σ - τ = t - (σ + τ) := by ring
  simp only [howland]
  rw [hU.cocycle, hsub]
