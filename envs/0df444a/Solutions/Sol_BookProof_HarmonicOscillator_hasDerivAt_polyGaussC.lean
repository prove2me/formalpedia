-- Prove2me | solution 1 for BookProof.HarmonicOscillator.hasDerivAt_polyGaussC
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:42:28.264172+00:00
-- url     : https://prove2.me/submissions/b22174b3-81b8-4b08-93dd-bfe659cd4e5a

-- Generated from ChapterHarmonicOscillatorEsa.lean — solution of BookProof.HarmonicOscillator.hasDerivAt_polyGaussC
import Mathlib
import Definitions.Def_ChapterHarmonicOscillatorEsa
import Theorems.Thm_BookProof_HermiteCore_hasDerivAt_poly_mul_gaussH
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HarmonicOscillator




open MeasureTheory Polynomial BookProof.HermiteCore BookProof.HermiteStrichartzQG
open BookProof.FarisLavine
open BookProof.HermiteCore

set_option maxHeartbeats 1000000 in
theorem solution (p : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (polyGaussC p)
      ((((derivative p - C (1 / 2 : ℝ) * (X * p)).eval x * gaussH x : ℝ) : ℂ)) x := (hasDerivAt_poly_mul_gaussH p x).ofReal_comp
