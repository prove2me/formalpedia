-- Prove2me | solution 1 for BookProof.ChapterDisplacedThermalMulti.dtBornMulti_eq_softmax
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:56:48.338089+00:00
-- url     : https://prove2.me/submissions/5fd9342d-56a5-4142-a1a5-c11cf288ad70
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterDisplacedThermalMulti.lean — solution of BookProof.ChapterDisplacedThermalMulti.dtBornMulti_eq_softmax
import Mathlib
import Definitions.Def_ChapterDisplacedThermalMulti
import Theorems.Thm_BookProof_ChapterDisplacedThermalMulti_dtOverlapMulti_eq
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterDisplacedThermalMulti



noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal


open BookProof.ChapterDisplacedThermalOverlap

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (nbar : ℝ≥0) (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) :
    dtBornMulti nbar q k j
      = BookProof.ChapterSoftmaxSharpness.scoreSoftmax (inverseTemperature nbar)
          (fun l => -‖q - k l‖ ^ 2) j := by

  have hc : (0 : ℝ) < (Real.sqrt (4 * π * ((nbar : ℝ) + 1 / 2))) ^ n := by
    have : (0 : ℝ) < Real.sqrt (4 * π * ((nbar : ℝ) + 1 / 2)) :=
      Real.sqrt_pos.mpr (by positivity)
    positivity
  have hval : ∀ l : Fin m, dtOverlapMulti nbar q (k l)
      = ((Real.sqrt (4 * π * ((nbar : ℝ) + 1 / 2))) ^ n)⁻¹
        * Real.exp (inverseTemperature nbar * (-‖q - k l‖ ^ 2)) := by
    intro l
    rw [dtOverlapMulti_eq, inverseTemperature, div_eq_inv_mul]
    congr 2
    field_simp
  simp only [dtBornMulti, BookProof.ChapterSoftmaxSharpness.scoreSoftmax, hval]
  rw [← Finset.mul_sum, mul_div_mul_left _ _ (inv_ne_zero (ne_of_gt hc))]
