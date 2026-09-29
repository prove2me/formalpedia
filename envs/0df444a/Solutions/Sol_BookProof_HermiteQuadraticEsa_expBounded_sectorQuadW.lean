-- Prove2me | solution 1 for BookProof.HermiteQuadraticEsa.expBounded_sectorQuadW
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:01:36.429295+00:00
-- url     : https://prove2.me/submissions/215af86e-f53c-4660-9896-472e10a819a2

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.expBounded_sectorQuadW
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

theorem setup_helper_abs_sectorQuadW_sub_harmW_le (M alpha mu : ℝ) (x : Vd 2) :
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

theorem setup_helper_expBounded_of_growth_bound {U : Vd d → ℝ} {A Ccoef B : ℝ} (hA : 0 ≤ A)
    (hC : 0 ≤ Ccoef) (hB : 0 ≤ B)
    (hU : ∀ x, |U x - harmW x| ≤ A * ‖x‖ ^ 2 + Ccoef * ‖x‖ + B) :
    ExpBounded U := by
  refine setup_helper_expBounded_of_le_harm (a := 4 * A + 1 + Ccoef) (b := Ccoef + B) (by positivity)
    (by positivity) fun x => ?_
  have h := hU x
  have hharm : harmW x = ‖x‖ ^ 2 / 4 := rfl
  have hlin : Ccoef * ‖x‖ ≤ Ccoef * (‖x‖ ^ 2 / 4 + 1) :=
    mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (‖x‖ - 2)]) hC
  have hsplit : U x = (U x - harmW x) + harmW x := by ring
  have habs : |U x| ≤ |U x - harmW x| + |harmW x| := by
    calc |U x| = |(U x - harmW x) + harmW x| := by rw [← hsplit]
      _ ≤ |U x - harmW x| + |harmW x| := abs_add_le _ _
  have hharm0 : |harmW x| = ‖x‖ ^ 2 / 4 := by
    rw [hharm, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x‖ ^ 2 / 4)]
  rw [hharm]
  rw [hharm0] at habs
  nlinarith [norm_nonneg x]

theorem solution (M alpha mu : ℝ) : ExpBounded (sectorQuadW M alpha mu) := setup_helper_expBounded_of_growth_bound (le_trans (abs_nonneg _) (le_max_left _ _)) (by positivity) le_rfl
    (setup_helper_abs_sectorQuadW_sub_harmW_le M alpha mu)

#print axioms solution
