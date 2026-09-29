-- Prove2me | solution 1 for BookProof.GaussCoreQuadBounds.eval_cpoly_self_re
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-12T13:45:22.220931+00:00
-- url     : https://prove2.me/submissions/4825d1ee-381b-4ea9-aa8e-957e2ac72893

import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds
open BookProof.QgHermiteFriedrichs
open BookProof.HermiteProductCore
open MvPolynomial

variable {D : ℕ}

theorem solution (q : MvPolynomial (Fin D) ℂ) (x : Vd D) :
    (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (cpoly q * q)).re
      = ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q‖ ^ 2 := by
  set g : Fin D → ℂ := fun i => ((x i : ℝ) : ℂ)
  have hg (i : Fin D) : starRingEnd ℂ (g i) = g i := by
    simp [g, Complex.conj_ofReal]
  have hmap : eval g (cpoly q) = starRingEnd ℂ (eval g q) := by
    unfold cpoly
    induction q using MvPolynomial.induction_on with
    | C a =>
      simp [eval_C, map_C]
    | add p r hp hr =>
      simp [map_add, eval_add, hp, hr]
    | mul_X p i hp =>
      simp [map_mul, map_X, eval_mul, eval_X, hp, hg]
  change (eval g (cpoly q * q)).re = ‖eval g q‖ ^ 2
  rw [eval_mul, hmap, mul_comm, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]
