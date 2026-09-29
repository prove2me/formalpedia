-- Prove2me | solution 1 for BookProof.GaussCoreQuadBounds.norm_pgLp_sq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-12T14:30:43.836869+00:00
-- url     : https://prove2.me/submissions/8e4ed8c3-d9d9-4c3d-962d-be81ed8c09d9

import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds
open BookProof.QgHermiteFriedrichs
open BookProof.HermiteProductCore
open MvPolynomial
open MeasureTheory

variable {D : ℕ}

theorem solution (q : MvPolynomial (Fin D) ℂ) :
    ‖pgLp q‖ ^ 2 = (gaussInt (cpoly q * q)).re := by
  have hmap (x : Vd D) :
      eval (fun i => ((x i : ℝ) : ℂ)) (cpoly q)
        = starRingEnd ℂ (eval (fun i => ((x i : ℝ) : ℂ)) q) := by
    unfold cpoly
    induction q using MvPolynomial.induction_on with
    | C a => simp [eval_C, map_C]
    | add p r hp hr => simp [map_add, eval_add, hp, hr]
    | mul_X p i hp =>
      have hi : starRingEnd ℂ ((x i : ℝ) : ℂ) = ((x i : ℝ) : ℂ) := by
        simp [Complex.conj_ofReal]
      simp [map_mul, map_X, eval_mul, eval_X, hp, hi]
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (pgLp (d := D) q), inner_pgLp]
  have hcoe :
      (fun x : Vd D =>
          starRingEnd ℂ (pgFun q x) * (pgLp q : Vd D → ℂ) x) =ᵐ[volume]
        fun x => starRingEnd ℂ (pgFun q x) * pgFun q x := by
    filter_upwards [pgLp_coeFn (d := D) q] with x hx
    rw [hx]
  rw [integral_congr_ae hcoe]
  unfold gaussInt
  have hinter := integrable_gwFun (d := D) (cpoly q * q)
  change
      RCLike.re (∫ x : Vd D, starRingEnd ℂ (pgFun q x) * pgFun q x)
        = RCLike.re (∫ x : Vd D,
            eval (fun i => ((x i : ℝ) : ℂ)) (cpoly q * q) * (gaussWD x : ℂ))
  refine congrArg RCLike.re (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_))
  simp only [pgFun, eval_mul, hmap, gaussWD_eq_sq, map_mul]
  have hg : starRingEnd ℂ (gaussD x : ℂ) = (gaussD x : ℂ) := by
    simp [Complex.conj_ofReal]
  simp [hg]
  ring
