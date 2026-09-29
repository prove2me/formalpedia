-- Prove2me | solution 1 for BookProof.GaussCoreQuadBounds.sum_norm_sq_mul_le_of_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T19:06:06.699817+00:00
-- url     : https://prove2.me/submissions/19432d22-8996-4292-95c9-755cb5a76630

-- Generated from ChapterGaussCoreQuadBounds.lean — solution of BookProof.GaussCoreQuadBounds.sum_norm_sq_mul_le_of_pointwise
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
import Theorems.Thm_BookProof_GaussCoreQuadBounds_gaussInt_re_mono
import Theorems.Thm_BookProof_GaussCoreQuadBounds_norm_pgLp_sq
import Theorems.Thm_BookProof_GaussCoreQuadBounds_eval_cpoly_self_re
import Definitions.Def_ChapterHermiteProductCore
open BookProof.GaussCoreQuadBounds









open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {R : Type*} [Fintype R]
    {f : R → MvPolynomial (Fin D) ℂ} {g : R → MvPolynomial (Fin D) ℂ} {lam : ℝ}
    (h : ∀ x : Vd D, ∑ r : R, ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (f r)‖ ^ 2
      ≤ lam * ∑ r : R, ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (g r)‖ ^ 2)
    (p : MvPolynomial (Fin D) ℂ) :
    ∑ r : R, ‖pgLp (f r * p)‖ ^ 2 ≤ lam * ∑ r : R, ‖pgLp (g r * p)‖ ^ 2 := by

  have hL : ∑ r : R, ‖pgLp (f r * p)‖ ^ 2
      = (gaussInt (∑ r : R, cpoly (f r * p) * (f r * p))).re := by
    rw [gaussInt_sum, Complex.re_sum]
    exact Finset.sum_congr rfl fun r _ => norm_pgLp_sq _
  have hR : lam * ∑ r : R, ‖pgLp (g r * p)‖ ^ 2
      = (gaussInt (((lam : ℝ) : ℂ) • ∑ r : R, cpoly (g r * p) * (g r * p))).re := by
    rw [gaussInt_smul, Complex.re_ofReal_mul, gaussInt_sum, Complex.re_sum]
    congr 1
    exact Finset.sum_congr rfl fun r _ => norm_pgLp_sq _
  rw [hL, hR]
  refine gaussInt_re_mono fun x => ?_
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, Complex.re_ofReal_mul,
    map_sum, map_sum, Complex.re_sum, Complex.re_sum]
  have hcongr : ∀ (u : R → MvPolynomial (Fin D) ℂ),
      ∑ r : R, (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (cpoly (u r * p) * (u r * p))).re
        = (∑ r : R, ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (u r)‖ ^ 2)
            * ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p‖ ^ 2 := by
    intro u
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [eval_cpoly_self_re, map_mul, norm_mul, mul_pow]
  rw [hcongr f, hcongr g]
  have hx := h x
  nlinarith [hx, sq_nonneg (‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p‖)]
