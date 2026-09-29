-- Prove2me | solution 1 for BookProof.HermiteQuadraticEsa.expBounded_confW
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:01:34.077077+00:00
-- url     : https://prove2.me/submissions/5ae7506d-b946-4e08-9a73-658362d9b5c0

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.expBounded_confW
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

theorem setup_helper_abs_confW_sub_harmW_le (M alpha : ℝ) (x : Vd 1) :
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

theorem setup_helper_expBounded_of_le_harm {V : Vd d → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hV : ∀ x, |V x| ≤ a * harmW x + b) : ExpBounded V := by
  refine ⟨a / 2 + b, 1, zero_le_one, fun x => ?_⟩
  have h := Real.pow_div_factorial_le_exp ‖x‖ (norm_nonneg x) 2
  have hfac : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num
  rw [hfac] at h
  have h1 : (1 : ℝ) ≤ Real.exp ‖x‖ := Real.one_le_exp (norm_nonneg x)
  have hharm : harmW x = ‖x‖ ^ 2 / 4 := rfl
  have hVx := hV x
  rw [hharm] at hVx
  rw [one_mul]
  nlinarith

theorem solution (M alpha : ℝ) : ExpBounded (confW M alpha) := by
  refine setup_helper_expBounded_of_le_harm (a := 4 * |alpha - 1 / 4| + 1 + M ^ 2 / 2)
    (b := M ^ 2 / 2) (by positivity) (by positivity) fun x => ?_
  have h := setup_helper_abs_confW_sub_harmW_le M alpha x
  have hharm : harmW x = ‖x‖ ^ 2 / 4 := rfl
  have hlin : (M ^ 2 / 2) * ‖x‖ ≤ (M ^ 2 / 2) * (‖x‖ ^ 2 / 4 + 1) := by
    have : ‖x‖ ≤ ‖x‖ ^ 2 / 4 + 1 := by nlinarith [sq_nonneg (‖x‖ - 2)]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have habs : |confW M alpha x| ≤ |confW M alpha x - harmW x| + |harmW x| := by
    have hsplit : confW M alpha x = (confW M alpha x - harmW x) + harmW x := by ring
    calc |confW M alpha x| = |(confW M alpha x - harmW x) + harmW x| := by rw [← hsplit]
      _ ≤ |confW M alpha x - harmW x| + |harmW x| := abs_add_le _ _
  have hharm0 : |harmW x| = ‖x‖ ^ 2 / 4 := by
    rw [hharm, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x‖ ^ 2 / 4)]
  rw [hharm]
  rw [hharm0] at habs
  nlinarith [norm_nonneg x, abs_nonneg (alpha - 1 / 4)]

#print axioms solution
