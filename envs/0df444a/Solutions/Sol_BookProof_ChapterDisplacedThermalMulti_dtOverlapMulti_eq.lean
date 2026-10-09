-- Prove2me | solution 1 for BookProof.ChapterDisplacedThermalMulti.dtOverlapMulti_eq
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:55:50.254882+00:00
-- url     : https://prove2.me/submissions/9ca322ae-e74e-4d20-977d-d8a56141d604
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterDisplacedThermalMulti.lean — solution of BookProof.ChapterDisplacedThermalMulti.dtOverlapMulti_eq
import Mathlib
import Definitions.Def_ChapterDisplacedThermalMulti
import Theorems.Thm_BookProof_ChapterDisplacedThermalMulti_norm_sq_eq_sum
import Theorems.Thm_BookProof_ChapterDisplacedThermalOverlap_dtOverlap_eq
open BookProof.ChapterDisplacedThermalMulti



noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal


open BookProof.ChapterDisplacedThermalOverlap

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (nbar : ℝ≥0) (a b : EuclideanSpace ℝ (Fin n)) :
    dtOverlapMulti nbar a b
      = Real.exp (-‖a - b‖ ^ 2 / (4 * ((nbar : ℝ) + 1 / 2)))
        / (Real.sqrt (4 * π * ((nbar : ℝ) + 1 / 2))) ^ n := by

  have hτ : (0 : ℝ) < 4 * ((nbar : ℝ) + 1 / 2) := by positivity
  simp only [dtOverlapMulti, dtOverlap_eq]
  rw [Finset.prod_div_distrib, ← Real.exp_sum]
  congr 1
  · congr 1
    rw [norm_sq_eq_sum, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · simp
