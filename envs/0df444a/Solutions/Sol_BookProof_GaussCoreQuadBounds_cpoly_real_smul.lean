-- Prove2me | solution 1 for BookProof.GaussCoreQuadBounds.cpoly_real_smul
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-12T13:37:19.754691+00:00
-- url     : https://prove2.me/submissions/1c038853-9f10-4637-a5b1-6ef1b52d16d9

import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds
open BookProof.QgHermiteFriedrichs

variable {D : ℕ}

theorem solution (c : ℝ) (q : MvPolynomial (Fin D) ℂ) :
    cpoly (((c : ℝ) : ℂ) • q) = ((c : ℝ) : ℂ) • cpoly q := by
  unfold cpoly
  ext m
  simp [MvPolynomial.coeff_map, MvPolynomial.coeff_smul, smul_eq_mul, map_mul,
    Complex.conj_ofReal]
