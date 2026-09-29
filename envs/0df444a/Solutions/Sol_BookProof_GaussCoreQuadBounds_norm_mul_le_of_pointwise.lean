-- Prove2me | solution 1 for BookProof.GaussCoreQuadBounds.norm_mul_le_of_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T19:06:06.076934+00:00
-- url     : https://prove2.me/submissions/8a914be0-b95c-48c2-8dd8-19ad64e533ca

-- Generated from ChapterGaussCoreQuadBounds.lean — solution of BookProof.GaussCoreQuadBounds.norm_mul_le_of_pointwise
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
theorem solution {f g : MvPolynomial (Fin D) ℂ} {lam : ℝ} (hlam : 0 ≤ lam)
    (h : ∀ x : Vd D, ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) f‖
      ≤ lam * ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) g‖)
    (p : MvPolynomial (Fin D) ℂ) :
    ‖pgLp (f * p)‖ ≤ lam * ‖pgLp (g * p)‖ := by

  have hsq : ‖pgLp (f * p)‖ ^ 2 ≤ (lam * ‖pgLp (g * p)‖) ^ 2 := by
    have hmono : (gaussInt (cpoly (f * p) * (f * p))).re
        ≤ (gaussInt ((((lam ^ 2 : ℝ)) : ℂ) • (cpoly (g * p) * (g * p)))).re := by
      refine gaussInt_re_mono fun x => ?_
      have hval : (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ))
            (MvPolynomial.C (((lam ^ 2 : ℝ) : ℂ)) * (cpoly (g * p) * (g * p)))).re
          = lam ^ 2 * ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (g * p)‖ ^ 2 := by
        rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, Complex.re_ofReal_mul,
          eval_cpoly_self_re]
      rw [eval_cpoly_self_re, MvPolynomial.smul_eq_C_mul, hval]
      have hf := h x
      have hp : (0 : ℝ) ≤ ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p‖ := norm_nonneg _
      have hg : (0 : ℝ) ≤ ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) g‖ := norm_nonneg _
      have hff : (0 : ℝ) ≤ ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) f‖ := norm_nonneg _
      rw [map_mul, map_mul, norm_mul, norm_mul, mul_pow, mul_pow]
      have : ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) f‖ ^ 2
          ≤ lam ^ 2 * ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) g‖ ^ 2 := by
        nlinarith
      nlinarith [sq_nonneg (‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p‖)]
    rw [gaussInt_smul, Complex.re_ofReal_mul] at hmono
    rw [norm_pgLp_sq, mul_pow, norm_pgLp_sq]
    exact hmono
  have hrhs : 0 ≤ lam * ‖pgLp (g * p)‖ := mul_nonneg hlam (norm_nonneg _)
  nlinarith [norm_nonneg (pgLp (f * p))]
