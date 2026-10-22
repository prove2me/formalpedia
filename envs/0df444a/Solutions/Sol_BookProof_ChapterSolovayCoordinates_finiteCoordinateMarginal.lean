-- Prove2me | solution 1 for BookProof.ChapterSolovayCoordinates.finiteCoordinateMarginal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T16:00:26.905979+00:00
-- url     : https://prove2.me/submissions/1d0bce47-7fed-4a04-ac41-3f53ddd4424a

-- Generated from ChapterSolovayCoordinates.lean — solution of BookProof.ChapterSolovayCoordinates.finiteCoordinateMarginal
import Mathlib
import Definitions.Def_ChapterSolovayCoordinates
open BookProof.ChapterSolovayCoordinates



open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (I : Finset ℕ) :
    Measure.map I.restrict coordinateTailMeasure =
      Measure.pi (fun _ : I => standardGaussian) := by

  exact Measure.infinitePi_map_restrict (fun _ : ℕ => standardGaussian)
