-- Prove2me | solution 1 for BookProof.GaussCoreQuadBounds.gaussInt_re_mono
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-12T13:55:21.402493+00:00
-- url     : https://prove2.me/submissions/06d8aaaa-805b-44e5-8e74-0585dd3a0bd0

import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds
open BookProof.HermiteProductCore
open MvPolynomial
open MeasureTheory

variable {D : ℕ}

theorem solution {r s : MvPolynomial (Fin D) ℂ}
    (h : ∀ x : Vd D, (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) r).re
      ≤ (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) s).re) :
    (gaussInt r).re ≤ (gaussInt s).re := by
  unfold gaussInt
  have hr := integrable_gwFun (d := D) r
  have hs := integrable_gwFun (d := D) s
  change RCLike.re (∫ x : Vd D, eval (fun i => ((x i : ℝ) : ℂ)) r * (gaussWD x : ℂ))
      ≤ RCLike.re (∫ x : Vd D, eval (fun i => ((x i : ℝ) : ℂ)) s * (gaussWD x : ℂ))
  rw [← integral_re (𝕜 := ℂ) hr, ← integral_re (𝕜 := ℂ) hs]
  refine integral_mono hr.re hs.re ?_
  intro x
  change ((eval (fun i => ((x i : ℝ) : ℂ)) r * (gaussWD x : ℂ)).re)
      ≤ ((eval (fun i => ((x i : ℝ) : ℂ)) s * (gaussWD x : ℂ)).re)
  have hre (t : MvPolynomial (Fin D) ℂ) :
      ((eval (fun i => ((x i : ℝ) : ℂ)) t * (gaussWD x : ℂ)).re)
        = (eval (fun i => ((x i : ℝ) : ℂ)) t).re * gaussWD x := by
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [hre r, hre s]
  exact mul_le_mul_of_nonneg_right (h x) (Real.exp_nonneg _)
