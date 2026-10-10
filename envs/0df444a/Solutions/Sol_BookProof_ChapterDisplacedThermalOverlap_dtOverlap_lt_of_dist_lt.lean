-- Prove2me | solution 1 for BookProof.ChapterDisplacedThermalOverlap.dtOverlap_lt_of_dist_lt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:02:32.371984+00:00
-- url     : https://prove2.me/submissions/dcddede8-0728-446a-8f43-1a205ac8f2b2

-- Generated from ChapterDisplacedThermalOverlap.lean — solution of BookProof.ChapterDisplacedThermalOverlap.dtOverlap_lt_of_dist_lt
import Mathlib
import Definitions.Def_ChapterDisplacedThermalOverlap
import Theorems.Thm_BookProof_ChapterDisplacedThermalOverlap_dtOverlap_eq
open BookProof.ChapterDisplacedThermalOverlap



noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

set_option maxHeartbeats 1000000 in
theorem solution (nbar : ℝ≥0) {a b c : ℝ}
    (h : (a - b) ^ 2 < (a - c) ^ 2) : dtOverlap nbar a c < dtOverlap nbar a b := by

  have hden : (0 : ℝ) < Real.sqrt (4 * π * ((nbar : ℝ) + 1 / 2)) :=
    Real.sqrt_pos.mpr (by positivity)
  have hτ : (0 : ℝ) < 4 * ((nbar : ℝ) + 1 / 2) := by positivity
  rw [dtOverlap_eq, dtOverlap_eq]
  have hexp : Real.exp (-(a - c) ^ 2 / (4 * ((nbar : ℝ) + 1 / 2)))
      < Real.exp (-(a - b) ^ 2 / (4 * ((nbar : ℝ) + 1 / 2))) :=
    Real.exp_lt_exp.mpr (div_lt_div_of_pos_right (by linarith) hτ)
  gcongr
