-- Prove2me | solution 1 for BookProof.ChapterDisplacedThermalMulti.dtBornMulti_vacuum_eq_bornWeight
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:57:20.092033+00:00
-- url     : https://prove2.me/submissions/734ca480-a55a-406b-af22-50445b83e518

-- Generated from ChapterDisplacedThermalMulti.lean — solution of BookProof.ChapterDisplacedThermalMulti.dtBornMulti_vacuum_eq_bornWeight
import Mathlib
import Definitions.Def_ChapterDisplacedThermalMulti
import Theorems.Thm_BookProof_ChapterDisplacedThermalMulti_dtBornMulti_eq_softmax
import Theorems.Thm_BookProof_ChapterCoherentGeometry_bornWeight_eq_scoreSoftmax_neg_dist_sq
import Definitions.Def_ChapterDisplacedThermalOverlap
import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterDisplacedThermalMulti



noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal


open BookProof.ChapterDisplacedThermalOverlap

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) :
    dtBornMulti 0 (Real.sqrt 2 • q) (fun l => Real.sqrt 2 • k l) j
      = BookProof.ChapterSoftmaxBorn.bornWeight q k j := by

  have hscale : ∀ l : Fin m,
      -‖Real.sqrt 2 • q - Real.sqrt 2 • k l‖ ^ 2 = 2 * (-‖q - k l‖ ^ 2) := by
    intro l
    rw [← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2), Real.sq_sqrt (by norm_num)]
    ring
  rw [dtBornMulti_eq_softmax,
    BookProof.ChapterCoherentGeometry.bornWeight_eq_scoreSoftmax_neg_dist_sq]
  simp only [BookProof.ChapterSoftmaxSharpness.scoreSoftmax, hscale, inverseTemperature,
    NNReal.coe_zero]
  norm_num
  refine congrArg₂ _ ?_ (Finset.sum_congr rfl fun l _ => ?_) <;> ring_nf
