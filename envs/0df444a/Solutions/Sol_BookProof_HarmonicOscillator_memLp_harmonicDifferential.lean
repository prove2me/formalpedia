-- Prove2me | solution 1 for BookProof.HarmonicOscillator.memLp_harmonicDifferential
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:43:38.982996+00:00
-- url     : https://prove2.me/submissions/30bde707-be17-4c0f-bc4c-c93f837bb1ff

-- Generated from ChapterHarmonicOscillatorEsa.lean — solution of BookProof.HarmonicOscillator.memLp_harmonicDifferential
import Mathlib
import Definitions.Def_ChapterHarmonicOscillatorEsa
import Theorems.Thm_BookProof_HarmonicOscillator_hermiteC_oscillator
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HarmonicOscillator




open MeasureTheory Polynomial BookProof.HermiteCore BookProof.HermiteStrichartzQG
open BookProof.FarisLavine
open BookProof.HermiteCore

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) :
    MemLp (fun x : ℝ => -(deriv (deriv (hermiteC n)) x) + ((x ^ 2 / 4 : ℝ) : ℂ) * hermiteC n x)
      2 (volume : Measure ℝ) := by

  have h : (fun x : ℝ => -(deriv (deriv (hermiteC n)) x) + ((x ^ 2 / 4 : ℝ) : ℂ) * hermiteC n x)
      = fun x : ℝ => (((n : ℝ) + 1 / 2 : ℝ) : ℂ) * hermiteC n x := by
    funext x
    exact hermiteC_oscillator n x
  rw [h]
  exact (memLp_hermiteC n).const_mul _
