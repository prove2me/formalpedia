-- Prove2me | solution 1 for BookProof.ChapterDisplacedThermalMulti.norm_sq_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:53:57.655966+00:00
-- url     : https://prove2.me/submissions/1e231704-1854-418c-b67c-a634733c9f21

-- Generated from ChapterDisplacedThermalMulti.lean — solution of BookProof.ChapterDisplacedThermalMulti.norm_sq_eq_sum
import Mathlib
import Definitions.Def_ChapterDisplacedThermalMulti
open BookProof.ChapterDisplacedThermalMulti



noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal


open BookProof.ChapterDisplacedThermalOverlap

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (a b : EuclideanSpace ℝ (Fin n)) :
    ‖a - b‖ ^ 2 = ∑ i, (a i - b i) ^ 2 := by

  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
