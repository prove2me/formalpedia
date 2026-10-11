-- Prove2me | solution 1 for BookProof.HermiteExpWall.quadForm_scalaron_ge
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:10:33.514176+00:00
-- url     : https://prove2.me/submissions/4e9ea78d-ef00-4986-8c0f-ffa85a2b8cae

-- Generated from ChapterHermiteExpWall.lean — solution of BookProof.HermiteExpWall.quadForm_scalaron_ge
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Theorems.Thm_BookProof_HermiteExpWall_gaussMoment_eq_integral
import Theorems.Thm_BookProof_HermiteExpWall_gaussMoment_even_pos
import Theorems.Thm_BookProof_HermiteExpWall_integrable_exp_mul_pow_gaussW
import Theorems.Thm_BookProof_HermiteExpWall_gaussMoment_tilt_ge
import Theorems.Thm_BookProof_HermiteExpWall_psi_sq
import Theorems.Thm_BookProof_HermiteExpWall_gaussMoment_shift_eight
import Theorems.Thm_BookProof_HermiteCore_gaussW_pos
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.HermiteExpWall




open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore
open BookProof.GhostField
open BookProof.HermiteCore
open BookProof.Starobinsky

noncomputable section

set_option maxHeartbeats 1000000 in

theorem solution (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha) (N : ℕ) :
    (M ^ 4 / (16 * alpha)) *
        ((8 * (Real.sqrt (2 / 3) / M) ^ 8 / 315) * (N : ℝ) ^ 4 - 1) * gaussMoment (2 * N)
      ≤ ∫ x : ℝ, starobinskyV M alpha x * psi N x ^ 2 := by
  set s : ℝ := Real.sqrt (2 / 3) / M with hs
  set c0 : ℝ := M ^ 4 / (16 * alpha) with hc0
  have hc0pos : 0 < c0 := by rw [hc0]; positivity
  set P : ℝ → ℝ := fun x => x ^ (2 * N) * gaussW x with hP
  have hPnn : ∀ x, 0 ≤ P x := by
    intro x
    have h1 : 0 ≤ x ^ (2 * N) := (Even.pow_nonneg ⟨N, by ring⟩ x)
    have hg := (gaussW_pos x).le
    simp only [hP]; positivity
  have hPint : Integrable P := by
    have h := integrable_poly_mul_gaussW ((Polynomial.X : Polynomial ℝ) ^ (2 * N))
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [hP]
  have hI1 : Integrable (fun x : ℝ => Real.exp (-s * x) * P x) :=
    integrable_exp_mul_pow_gaussW (-s) (2 * N)
  have hI2 : Integrable (fun x : ℝ => Real.exp (-(2 * s) * x) * P x) :=
    integrable_exp_mul_pow_gaussW (-(2 * s)) (2 * N)
  have hid : ∀ x : ℝ, starobinskyV M alpha x * psi N x ^ 2
      = c0 * (P x - 2 * (Real.exp (-s * x) * P x) + Real.exp (-(2 * s) * x) * P x) := by
    intro x
    have harg : -(Real.sqrt (2 / 3)) * x / M = -s * x := by
      rw [hs]; field_simp
    have hsq : Real.exp (-(2 * s) * x) = Real.exp (-s * x) ^ 2 := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [starobinskyV, psi_sq, harg, hsq, ← hc0]
    simp only [hP]
    ring
  have hInt : ∫ x : ℝ, starobinskyV M alpha x * psi N x ^ 2
      = c0 * ((∫ x, P x) - 2 * (∫ x, Real.exp (-s * x) * P x)
        + ∫ x, Real.exp (-(2 * s) * x) * P x) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hid), integral_const_mul]
    congr 1
    have hA : Integrable (fun x : ℝ => P x - 2 * (Real.exp (-s * x) * P x)) := by
      exact hPint.sub (hI1.const_mul 2)
    rw [integral_add hA hI2, integral_sub hPint (hI1.const_mul 2), integral_const_mul]
  have hPm : ∫ x, P x = gaussMoment (2 * N) := by
    rw [gaussMoment_eq_integral]
  have hAM : 2 * (∫ x, Real.exp (-s * x) * P x)
      ≤ (1 / 2) * (∫ x, Real.exp (-(2 * s) * x) * P x) + 2 * (∫ x, P x) := by
    have hmono : ∀ x : ℝ, 2 * (Real.exp (-s * x) * P x)
        ≤ (1 / 2) * (Real.exp (-(2 * s) * x) * P x) + 2 * P x := by
      intro x
      have hsq : Real.exp (-(2 * s) * x) = Real.exp (-s * x) ^ 2 := by
        rw [← Real.exp_nat_mul]; ring_nf
      have hkey : 2 * Real.exp (-s * x) ≤ (1 / 2) * Real.exp (-s * x) ^ 2 + 2 := by
        nlinarith [sq_nonneg (Real.exp (-s * x) - 2)]
      rw [hsq]
      nlinarith [hPnn x, hkey]
    have hL : Integrable (fun x : ℝ => 2 * (Real.exp (-s * x) * P x)) := hI1.const_mul 2
    have hR : Integrable (fun x : ℝ =>
        (1 / 2) * (Real.exp (-(2 * s) * x) * P x) + 2 * P x) :=
      (hI2.const_mul _).add (hPint.const_mul 2)
    have hmi := integral_mono hL hR hmono
    rwa [integral_add (hI2.const_mul _) (hPint.const_mul 2), integral_const_mul,
      integral_const_mul, integral_const_mul] at hmi
  have htilt : (s ^ 8 / 315) * gaussMoment (2 * N + 8)
      ≤ ∫ x, Real.exp (-(2 * s) * x) * P x := gaussMoment_tilt_ge s N
  have hmpos := gaussMoment_even_pos N
  have hNnn : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hbig : 16 * (N:ℝ) ^ 4 * gaussMoment (2 * N) ≤ gaussMoment (2 * N + 8) := by
    rw [gaussMoment_shift_eight]
    have h : 16 * (N:ℝ) ^ 4
        ≤ (2 * (N:ℝ) + 7) * (2 * (N:ℝ) + 5) * (2 * (N:ℝ) + 3) * (2 * (N:ℝ) + 1) := by
      calc 16 * (N:ℝ) ^ 4 = (2 * (N:ℝ)) * (2 * (N:ℝ)) * (2 * (N:ℝ)) * (2 * (N:ℝ)) := by ring
        _ ≤ (2 * (N:ℝ) + 7) * (2 * (N:ℝ) + 5) * (2 * (N:ℝ) + 3) * (2 * (N:ℝ) + 1) := by
            gcongr <;> linarith
    exact mul_le_mul_of_nonneg_right h hmpos.le
  have hchain : (8 * s ^ 8 / 315) * (N:ℝ) ^ 4 * gaussMoment (2 * N)
      ≤ (1 / 2) * ∫ x, Real.exp (-(2 * s) * x) * P x := by
    have h1 : (s ^ 8 / 315) * (16 * (N:ℝ) ^ 4 * gaussMoment (2 * N))
        ≤ (s ^ 8 / 315) * gaussMoment (2 * N + 8) :=
      mul_le_mul_of_nonneg_left hbig (by positivity)
    nlinarith [htilt, h1]
  rw [hInt, hPm]
  nlinarith [hAM, hchain, hc0pos, hmpos]
