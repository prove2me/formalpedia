-- Prove2me | solution 1 for BookProof.HarmonicOscillator.hermiteC_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:42:41.152083+00:00
-- url     : https://prove2.me/submissions/9e64fc40-dc6a-42d6-9005-62df53782362

-- Generated from ChapterHarmonicOscillatorEsa.lean — solution of BookProof.HarmonicOscillator.hermiteC_eq
import Mathlib
import Definitions.Def_ChapterHarmonicOscillatorEsa
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HarmonicOscillator




open MeasureTheory Polynomial BookProof.HermiteCore BookProof.HermiteStrichartzQG
open BookProof.FarisLavine
open BookProof.HermiteCore

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) :
    hermiteC n = fun x => ((hermiteNorm n : ℝ) : ℂ)⁻¹ * polyGaussC (hermiteR n) x := by

  funext x
  simp only [hermiteC, hermiteFun, polyGaussC]
  push_cast
  ring
