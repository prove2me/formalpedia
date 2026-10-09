-- Prove2me | solution 1 for BookProof.ChapterDisplacedThermalMulti.dtOverlapMulti_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:54:57.095045+00:00
-- url     : https://prove2.me/submissions/00eb6e14-4522-48ba-a1b3-73768ce5238c

-- Generated from ChapterDisplacedThermalMulti.lean — solution of BookProof.ChapterDisplacedThermalMulti.dtOverlapMulti_eq_integral
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
theorem solution (nbar : ℝ≥0) (a b : EuclideanSpace ℝ (Fin n)) :
    dtOverlapMulti nbar a b
      = ∫ x : Fin n → ℝ, ∏ i, (gaussianPDFReal (a i) (tauNN nbar) (x i)
          * gaussianPDFReal (b i) (tauNN nbar) (x i)) := by

  rw [dtOverlapMulti,
    MeasureTheory.integral_fintype_prod_volume_eq_prod
      (fun i (y : ℝ) => gaussianPDFReal (a i) (tauNN nbar) y
        * gaussianPDFReal (b i) (tauNN nbar) y)]
  rfl
