-- Prove2me | solution 1 for BookProof.ChapterFreeFieldGaussian.charFun_stdGaussian
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T09:23:04.526083+00:00
-- url     : https://prove2.me/submissions/21c592d9-01ae-4ca3-af6d-8e20946d7e41

-- Generated from ChapterFreeFieldGaussian.lean — solution of BookProof.ChapterFreeFieldGaussian.charFun_stdGaussian
import Mathlib
import Definitions.Def_ChapterFreeFieldGaussian
open BookProof.ChapterFreeFieldGaussian



open MeasureTheory ProbabilityTheory Complex WithLp
open scoped RealInnerProductSpace ENNReal


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (t : EuclideanSpace ℝ (Fin n)) :
    charFun (stdGaussian n) t = Complex.exp (-‖t‖ ^ 2 / 2) := by

  show charFun ((Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map (toLp 2)) t = _
  rw [ProbabilityTheory.map_pi_eq_stdGaussian]
  exact ProbabilityTheory.charFun_stdGaussian t
