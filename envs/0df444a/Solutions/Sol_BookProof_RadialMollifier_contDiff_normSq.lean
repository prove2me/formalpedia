-- Prove2me | solution 1 for BookProof.RadialMollifier.contDiff_normSq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:49:23.738697+00:00
-- url     : https://prove2.me/submissions/4ffb8d0d-6a49-4849-9629-92147dd5b6d6

-- Generated from ChapterRadialMollifier.lean — solution of BookProof.RadialMollifier.contDiff_normSq
import Mathlib
import Definitions.Def_ChapterRadialMollifier
open BookProof.RadialMollifier




open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution : ContDiff ℝ ∞ (fun z : ℂ => Complex.normSq z) := by

  simp only [Complex.normSq_apply]
  exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
    (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
