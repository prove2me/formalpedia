-- Prove2me | solution 1 for BookProof.GaussCoreQuadBounds.coreD_comm
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-12T14:10:28.121968+00:00
-- url     : https://prove2.me/submissions/00da2849-2641-474d-b356-9e9075b5b767

import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds
open BookProof.QgHermiteFriedrichs
open MvPolynomial

variable {D : ℕ}

theorem solution (j k : Fin D) (p : MvPolynomial (Fin D) ℂ) :
    coreD j (coreD k p) = coreD k (coreD j p) := by
  have pderiv_comm (q : MvPolynomial (Fin D) ℂ) :
      pderiv j (pderiv k q) = pderiv k (pderiv j q) := by
    ext m
    simp only [coeff_pderiv]
    have hadd :
        m + Finsupp.single j 1 + Finsupp.single k 1 =
          m + Finsupp.single k 1 + Finsupp.single j 1 := by
      ac_rfl
    rw [hadd, Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_apply,
      Finsupp.single_apply]
    by_cases h : j = k
    · subst h; ring
    · simp [h, mt Eq.symm h]; ring
  unfold coreD
  simp only [map_sub, pderiv_mul, pderiv_C, pderiv_C_mul, zero_mul, sub_zero, pderiv_X,
    Pi.single_apply]
  rw [pderiv_comm p]
  by_cases h : j = k
  · subst h; ring
  · simp [h, mt Eq.symm h]; ring
