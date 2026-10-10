-- Prove2me | solution 1 for BookProof.HermiteExpWall.gaussMoment_tilt_ge
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:03:27.092924+00:00
-- url     : https://prove2.me/submissions/a57b1aac-d032-4141-909e-068828255b39

-- Generated from ChapterHermiteExpWall.lean — solution of BookProof.HermiteExpWall.gaussMoment_tilt_ge
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Theorems.Thm_BookProof_HermiteExpWall_gaussMoment_eq_integral
import Theorems.Thm_BookProof_HermiteExpWall_integrable_exp_mul_pow_gaussW
import Theorems.Thm_BookProof_HermiteExpWall_abs_pow_eight
import Theorems.Thm_BookProof_HermiteCore_gaussW_pos
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteExpWall




open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore
open BookProof.HermiteCore

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (s : ℝ) (N : ℕ) :
    (s ^ 8 / 315) * gaussMoment (2 * N + 8)
      ≤ ∫ x : ℝ, Real.exp (-(2 * s) * x) * (x ^ (2 * N) * gaussW x) := by

  set F : ℝ → ℝ := fun x => Real.exp (-(2 * s) * x) * (x ^ (2 * N) * gaussW x) with hF
  set G : ℝ → ℝ := fun x => Real.exp ((2 * s) * x) * (x ^ (2 * N) * gaussW x) with hG
  have hFint : Integrable F := integrable_exp_mul_pow_gaussW (-(2 * s)) (2 * N)
  have hGint : Integrable G := integrable_exp_mul_pow_gaussW (2 * s) (2 * N)
  have hFG : ∫ x, G x = ∫ x, F x := by
    have h := integral_neg_eq_self F volume
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hF, hG, gaussW]
    rw [show ((-x) ^ (2 * N) : ℝ) = x ^ (2 * N) from (Even.neg_pow ⟨N, by ring⟩ x)]
    ring_nf
  have hpoly : Integrable
      (fun x : ℝ => ((2 * s) ^ 8 / 40320) * (x ^ (2 * N + 8) * gaussW x)) := by
    have h := (integrable_poly_mul_gaussW ((Polynomial.X : Polynomial ℝ) ^ (2 * N + 8))).const_mul
      ((2 * s) ^ 8 / 40320)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp
  have hmono : ∀ x : ℝ, ((2 * s) ^ 8 / 40320) * (x ^ (2 * N + 8) * gaussW x) ≤ F x + G x := by
    intro x
    have hnn : 0 ≤ x ^ (2 * N) * gaussW x := by
      have h1 : 0 ≤ x ^ (2 * N) := (Even.pow_nonneg ⟨N, by ring⟩ x)
      have hg := (gaussW_pos x).le
      positivity
    have hexp : ((2 * s) ^ 8 / 40320) * x ^ 8
        ≤ Real.exp (-(2 * s) * x) + Real.exp ((2 * s) * x) := by
      have h1 : |2 * s * x| ^ 8 / (Nat.factorial 8 : ℝ) ≤ Real.exp |2 * s * x| :=
        Real.pow_div_factorial_le_exp _ (abs_nonneg _) 8
      have h2 : |2 * s * x| ^ 8 = (2 * s) ^ 8 * x ^ 8 := by
        rw [abs_mul, mul_pow, abs_pow_eight, abs_pow_eight]
      have h3 : Real.exp |2 * s * x| ≤ Real.exp (-(2 * s) * x) + Real.exp ((2 * s) * x) := by
        rcases abs_cases (2 * s * x) with ⟨he, -⟩ | ⟨he, -⟩
        · rw [he]
          nlinarith [Real.exp_pos (-(2 * s) * x)]
        · rw [he, show -(2 * s * x) = -(2 * s) * x by ring]
          nlinarith [Real.exp_pos ((2 * s) * x)]
      have hfac : (Nat.factorial 8 : ℝ) = 40320 := by norm_num [Nat.factorial]
      rw [h2, hfac] at h1
      calc ((2 * s) ^ 8 / 40320) * x ^ 8 = (2 * s) ^ 8 * x ^ 8 / 40320 := by ring
        _ ≤ Real.exp |2 * s * x| := h1
        _ ≤ _ := h3
    calc ((2 * s) ^ 8 / 40320) * (x ^ (2 * N + 8) * gaussW x)
        = (((2 * s) ^ 8 / 40320) * x ^ 8) * (x ^ (2 * N) * gaussW x) := by ring
      _ ≤ (Real.exp (-(2 * s) * x) + Real.exp ((2 * s) * x)) * (x ^ (2 * N) * gaussW x) :=
          mul_le_mul_of_nonneg_right hexp hnn
      _ = F x + G x := by simp only [hF, hG]; ring
  have hint : ∫ x : ℝ, ((2 * s) ^ 8 / 40320) * (x ^ (2 * N + 8) * gaussW x)
      ≤ ∫ x, (F x + G x) := integral_mono hpoly (hFint.add hGint) hmono
  rw [integral_add hFint hGint, hFG, integral_const_mul, ← gaussMoment_eq_integral] at hint
  nlinarith [hint]
