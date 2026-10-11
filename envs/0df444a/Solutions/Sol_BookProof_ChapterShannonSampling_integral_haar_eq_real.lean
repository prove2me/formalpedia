-- Prove2me | solution 1 for BookProof.ChapterShannonSampling.integral_haar_eq_real
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:32:51.230858+00:00
-- url     : https://prove2.me/submissions/efb8d631-7126-4abc-be94-f452fe00cfd1

-- Generated from ChapterShannonSampling.lean — solution of BookProof.ChapterShannonSampling.integral_haar_eq_real
import Mathlib
import Definitions.Def_ChapterShannonSampling
open BookProof.ChapterShannonSampling




open MeasureTheory Complex AddCircle intervalIntegral Set
open scoped Real ComplexConjugate

variable {T : ℝ} [hT : Fact (0 < T)]

set_option maxHeartbeats 1000000 in
theorem solution (g : AddCircle T → ℝ) :
    T * ∫ z : AddCircle T, g z ∂haarAddCircle
      = ∫ ξ in (-(T / 2))..(-(T / 2) + T), g ξ := by

  rw [AddCircle.intervalIntegral_preimage, AddCircle.volume_eq_smul_haarAddCircle,
    MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal hT.out.le]
  simp [smul_eq_mul]
