-- Prove2me | solution 1 for BookProof.HermiteQuadraticEsa.abs_confW_sub_harmW_le
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:01:22.127212+00:00
-- url     : https://prove2.me/submissions/6d9ab15e-2c07-4a57-a002-fe7975feed0d

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.abs_confW_sub_harmW_le
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem setup_helper_norm_sq_one (x : Vd 1) : ‖x‖ ^ 2 = (x 0) ^ 2 := by
  rw [norm_sq_eq_sum x, Fin.sum_univ_one]

theorem setup_helper_abs_coord_le_norm (x : Vd 1) : |x 0| ≤ ‖x‖ := by
  have h := setup_helper_norm_sq_one x
  nlinarith [abs_nonneg (x 0), norm_nonneg x, sq_abs (x 0)]

theorem solution (M alpha : ℝ) (x : Vd 1) :
    |confW M alpha x - harmW x| ≤ |alpha - 1 / 4| * ‖x‖ ^ 2 + (M ^ 2 / 2) * ‖x‖ + 0 := by
  have hsq := setup_helper_norm_sq_one x
  have habs := setup_helper_abs_coord_le_norm x
  have hharm : harmW x = ‖x‖ ^ 2 / 4 := rfl
  have hsplit : confW M alpha x - harmW x
      = (alpha - 1 / 4) * (x 0) ^ 2 - (M ^ 2 / 2) * (x 0) := by
    unfold confW confV
    rw [hharm, hsq]
    ring
  rw [hsplit]
  have h1 : |(alpha - 1 / 4) * (x 0) ^ 2 - (M ^ 2 / 2) * (x 0)|
      ≤ |(alpha - 1 / 4) * (x 0) ^ 2| + |(M ^ 2 / 2) * (x 0)| := abs_sub _ _
  have h2 : |(alpha - 1 / 4) * (x 0) ^ 2| = |alpha - 1 / 4| * ‖x‖ ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (x 0)), hsq]
  have h3 : |(M ^ 2 / 2) * (x 0)| ≤ (M ^ 2 / 2) * ‖x‖ := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ M ^ 2 / 2)]
    exact mul_le_mul_of_nonneg_left habs (by positivity)
  linarith

#print axioms solution
