-- Prove2me | solution 1 for BookProof.HarmonicOscillator.harmonicOsc_not_bounded
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:03:39.619399+00:00
-- url     : https://prove2.me/submissions/50c57b10-70c7-4e0b-805a-4196b972ba64

-- Generated from ChapterHarmonicOscillatorEsa.lean — solution of BookProof.HarmonicOscillator.harmonicOsc_not_bounded
import Mathlib
import Definitions.Def_ChapterHarmonicOscillatorEsa
import Theorems.Thm_BookProof_HermiteStrichartzQG_hermiteCoreOp_not_bounded
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavine
open BookProof.HarmonicOscillator




open MeasureTheory Polynomial BookProof.HermiteCore BookProof.HermiteStrichartzQG
open BookProof.FarisLavine

set_option maxHeartbeats 1000000 in
theorem solution :
    ¬ ∃ C : ℝ, ∀ f : hermiteCore, ‖harmonicOscOp f‖ ≤ C * ‖(f : L2R)‖ := by

  refine hermiteCoreOp_not_bounded harmonicSymbol fun C => ?_
  obtain ⟨n, hn⟩ := exists_nat_gt C
  refine ⟨n, ?_⟩
  have h : |harmonicSymbol n| = (n : ℝ) + 1 / 2 := by
    rw [harmonicSymbol, abs_of_nonneg (by positivity)]
  rw [h]
  linarith
