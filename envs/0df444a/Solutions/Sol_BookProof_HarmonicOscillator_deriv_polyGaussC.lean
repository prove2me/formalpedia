-- Prove2me | solution 1 for BookProof.HarmonicOscillator.deriv_polyGaussC
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:42:39.907042+00:00
-- url     : https://prove2.me/submissions/3ec2825c-d16c-4414-95c6-f2c25015be40

-- Generated from ChapterHarmonicOscillatorEsa.lean — solution of BookProof.HarmonicOscillator.deriv_polyGaussC
import Mathlib
import Definitions.Def_ChapterHarmonicOscillatorEsa
import Theorems.Thm_BookProof_HarmonicOscillator_hasDerivAt_polyGaussC
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HarmonicOscillator




open MeasureTheory Polynomial BookProof.HermiteCore BookProof.HermiteStrichartzQG
open BookProof.FarisLavine
open BookProof.HermiteCore

set_option maxHeartbeats 1000000 in
theorem solution (p : Polynomial ℝ) :
    deriv (polyGaussC p) = polyGaussC (derivative p - C (1 / 2 : ℝ) * (X * p)) := funext fun x => (hasDerivAt_polyGaussC p x).deriv
