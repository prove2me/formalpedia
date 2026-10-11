-- Prove2me | solution 1 for BookProof.RadialMollifier.continuous_polarSymm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:51:04.465138+00:00
-- url     : https://prove2.me/submissions/aaf8244c-8103-483f-9097-088ae8c5e566

-- Generated from ChapterRadialMollifier.lean — solution of BookProof.RadialMollifier.continuous_polarSymm
import Mathlib
import Definitions.Def_ChapterRadialMollifier
open BookProof.RadialMollifier




open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by

  simp only [Complex.polarCoord_symm_apply]
  fun_prop
