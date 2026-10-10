-- Prove2me | solution 1 for BookProof.HarmonicOscillator.deriv_const_mul_fun
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:42:52.746335+00:00
-- url     : https://prove2.me/submissions/249e1731-8010-42dc-a49b-b8ec68204353

-- Generated from ChapterHarmonicOscillatorEsa.lean — solution of BookProof.HarmonicOscillator.deriv_const_mul_fun
import Mathlib
import Definitions.Def_ChapterHarmonicOscillatorEsa
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavine
open BookProof.HarmonicOscillator




open MeasureTheory Polynomial BookProof.HermiteCore BookProof.HermiteStrichartzQG
open BookProof.FarisLavine

set_option maxHeartbeats 1000000 in
theorem solution (c : ℂ) {f : ℝ → ℂ} (hf : ∀ x, DifferentiableAt ℝ f x) :
    deriv (fun x => c * f x) = fun x => c * deriv f x := funext fun x => deriv_const_mul c (hf x)
