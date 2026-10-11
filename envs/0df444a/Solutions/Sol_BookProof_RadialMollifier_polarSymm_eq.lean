-- Prove2me | solution 1 for BookProof.RadialMollifier.polarSymm_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:51:22.341702+00:00
-- url     : https://prove2.me/submissions/596ad154-25dc-40f8-b437-7559aee47470

-- Generated from ChapterRadialMollifier.lean — solution of BookProof.RadialMollifier.polarSymm_eq
import Mathlib
import Definitions.Def_ChapterRadialMollifier
open BookProof.RadialMollifier




open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (r θ : ℝ) :
    Complex.polarCoord.symm (r, θ) = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by

  rw [Complex.exp_mul_I]
  simp [Complex.polarCoord_symm_apply]
