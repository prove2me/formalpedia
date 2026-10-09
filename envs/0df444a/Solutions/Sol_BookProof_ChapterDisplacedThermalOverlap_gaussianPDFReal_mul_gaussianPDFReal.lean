-- Prove2me | solution 1 for BookProof.ChapterDisplacedThermalOverlap.gaussianPDFReal_mul_gaussianPDFReal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:00:35.867777+00:00
-- url     : https://prove2.me/submissions/3a0a3934-b293-4aa4-a5b4-7dacd544c46e

-- Generated from ChapterDisplacedThermalOverlap.lean — solution of BookProof.ChapterDisplacedThermalOverlap.gaussianPDFReal_mul_gaussianPDFReal
import Mathlib
import Definitions.Def_ChapterDisplacedThermalOverlap
open BookProof.ChapterDisplacedThermalOverlap



noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

set_option maxHeartbeats 1000000 in
theorem solution (a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    gaussianPDFReal a v x * gaussianPDFReal b v x
      = (Real.exp (-(a - b) ^ 2 / (4 * (v : ℝ))) / Real.sqrt (4 * π * v))
        * gaussianPDFReal ((a + b) / 2) (v / 2) x := by

  have hV : (0 : ℝ) < (v : ℝ) := by positivity
  have hhalf : (((v / 2 : ℝ≥0)) : ℝ) = (v : ℝ) / 2 := by push_cast; ring
  have h1 : Real.sqrt (2 * π * v) * Real.sqrt (2 * π * v) = 2 * π * (v : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  have hexp : rexp (-(x - a) ^ 2 / (2 * (v : ℝ))) * rexp (-(x - b) ^ 2 / (2 * (v : ℝ)))
      = rexp (-(a - b) ^ 2 / (4 * (v : ℝ)))
        * rexp (-(x - (a + b) / 2) ^ 2 / (2 * ((v : ℝ) / 2))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  simp only [gaussianPDFReal, hhalf]
  rw [show ((√(2 * π * (v : ℝ)))⁻¹ * rexp (-(x - a) ^ 2 / (2 * (v : ℝ))))
      * ((√(2 * π * (v : ℝ)))⁻¹ * rexp (-(x - b) ^ 2 / (2 * (v : ℝ))))
      = ((√(2 * π * (v : ℝ))) * (√(2 * π * (v : ℝ))))⁻¹
        * (rexp (-(x - a) ^ 2 / (2 * (v : ℝ))) * rexp (-(x - b) ^ 2 / (2 * (v : ℝ)))) by
    rw [mul_inv]; ring]
  rw [h1, hexp, div_eq_mul_inv]
  have h4 : (0 : ℝ) < Real.sqrt (4 * π * (v : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have h2 : Real.sqrt (π * (v : ℝ) * 4) * Real.sqrt (π * (v : ℝ)) = 2 * π * (v : ℝ) := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show (π * (v : ℝ) * 4) * (π * (v : ℝ)) = (2 * π * (v : ℝ)) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  field_simp
  linarith [h2]
