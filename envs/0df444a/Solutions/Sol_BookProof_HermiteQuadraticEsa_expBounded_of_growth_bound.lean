-- Prove2me | solution 1 for BookProof.HermiteQuadraticEsa.expBounded_of_growth_bound
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:01:34.852383+00:00
-- url     : https://prove2.me/submissions/4aae657f-f773-419a-bafc-af2c4587a304

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.expBounded_of_growth_bound
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

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

theorem solution {U : Vd d → ℝ} {A Ccoef B : ℝ} (hA : 0 ≤ A)
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

#print axioms solution
