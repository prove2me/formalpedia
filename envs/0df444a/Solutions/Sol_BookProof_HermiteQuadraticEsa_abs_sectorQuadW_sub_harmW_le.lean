-- Prove2me | solution 1 for BookProof.HermiteQuadraticEsa.abs_sectorQuadW_sub_harmW_le
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:01:26.921346+00:00
-- url     : https://prove2.me/submissions/78b6060f-4d59-4da5-9fa1-8f914d0d2cd1

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.abs_sectorQuadW_sub_harmW_le
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem setup_helper_norm_sq_two (x : Vd 2) : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
  rw [norm_sq_eq_sum x, Fin.sum_univ_two]

theorem setup_helper_abs_coord_zero_le_norm_two (x : Vd 2) : |x 0| ≤ ‖x‖ := by
  have h := setup_helper_norm_sq_two x
  nlinarith [abs_nonneg (x 0), norm_nonneg x, sq_abs (x 0), sq_nonneg (x 1)]

theorem solution (M alpha mu : ℝ) (x : Vd 2) :
    |sectorQuadW M alpha mu x - harmW x|
      ≤ max |alpha - 1 / 4| |mu - 1 / 4| * ‖x‖ ^ 2 + (M ^ 2 / 2) * ‖x‖ + 0 := by
  have hsq := setup_helper_norm_sq_two x
  have hc0 := setup_helper_abs_coord_zero_le_norm_two x
  have hharm : harmW x = ‖x‖ ^ 2 / 4 := rfl
  have hsplit : sectorQuadW M alpha mu x - harmW x
      = (alpha - 1 / 4) * (x 0) ^ 2 + (mu - 1 / 4) * (x 1) ^ 2 - (M ^ 2 / 2) * (x 0) := by
    unfold sectorQuadW confV
    rw [hharm, hsq]
    ring
  have hmax0 : |alpha - 1 / 4| ≤ max |alpha - 1 / 4| |mu - 1 / 4| := le_max_left _ _
  have hmax1 : |mu - 1 / 4| ≤ max |alpha - 1 / 4| |mu - 1 / 4| := le_max_right _ _
  have t1 := abs_sub ((alpha - 1 / 4) * (x 0) ^ 2 + (mu - 1 / 4) * (x 1) ^ 2)
    ((M ^ 2 / 2) * (x 0))
  have t2 := abs_add_le ((alpha - 1 / 4) * (x 0) ^ 2) ((mu - 1 / 4) * (x 1) ^ 2)
  have e0 : |(alpha - 1 / 4) * (x 0) ^ 2| = |alpha - 1 / 4| * (x 0) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (x 0))]
  have e1 : |(mu - 1 / 4) * (x 1) ^ 2| = |mu - 1 / 4| * (x 1) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (x 1))]
  have e2 : |(M ^ 2 / 2) * (x 0)| ≤ (M ^ 2 / 2) * ‖x‖ := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ M ^ 2 / 2)]
    exact mul_le_mul_of_nonneg_left hc0 (by positivity)
  have b0 : |alpha - 1 / 4| * (x 0) ^ 2 ≤ max |alpha - 1 / 4| |mu - 1 / 4| * (x 0) ^ 2 :=
    mul_le_mul_of_nonneg_right hmax0 (sq_nonneg _)
  have b1 : |mu - 1 / 4| * (x 1) ^ 2 ≤ max |alpha - 1 / 4| |mu - 1 / 4| * (x 1) ^ 2 :=
    mul_le_mul_of_nonneg_right hmax1 (sq_nonneg _)
  have hAsum : max |alpha - 1 / 4| |mu - 1 / 4| * ‖x‖ ^ 2
      = max |alpha - 1 / 4| |mu - 1 / 4| * (x 0) ^ 2
        + max |alpha - 1 / 4| |mu - 1 / 4| * (x 1) ^ 2 := by
    rw [hsq]; ring
  rw [hsplit]
  linarith

#print axioms solution
