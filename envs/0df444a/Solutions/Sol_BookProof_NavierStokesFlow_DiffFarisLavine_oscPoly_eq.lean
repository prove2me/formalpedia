-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DiffFarisLavine.oscPoly_eq
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:05:59.391348+00:00
-- url     : https://prove2.me/submissions/1e310baa-fb76-4bbd-ac12-df568c85e51f

-- Adapted from Leonardo Pedro, timepiece commit 61595bc, Apache-2.0.
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDiffFarisLavine.lean
import Definitions.Def_ChapterNavierStokesDiffFarisLavine
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 4000000
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.DiffFarisLavine
open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine
open BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.DifferentialL2

private theorem momPoly_apply (i : Fin 3) (p : MvPolynomial (Fin 3) ℂ) :
    momPoly i p = C (-Complex.I) * (pderiv i p - C (1/2 : ℂ) * (X i * p)) := rfl
private theorem crePoly_apply (i : Fin 3) (p : MvPolynomial (Fin 3) ℂ) :
    crePoly i p = X i * p - pderiv i p := rfl
private theorem annPoly_apply (i : Fin 3) (p : MvPolynomial (Fin 3) ℂ) :
    annPoly i p = pderiv i p := rfl
private theorem mulXPoly_apply (i : Fin 3) (p : MvPolynomial (Fin 3) ℂ) :
    mulXPoly i p = X i * p := rfl

theorem solution (i : Fin 3) (p : MvPolynomial (Fin 3) ℂ) :
    momPoly i (momPoly i p) + mulXPoly i (mulXPoly i (((1 / 4 : ℂ)) • p))
      = crePoly i (annPoly i p) + ((1 / 2 : ℂ)) • p := by
  have hL : pderiv i (X i * p) = p + X i * pderiv i p := by
    rw [Derivation.leibniz, pderiv_X_self]
    simp [smul_eq_mul]
    ring
  have hd : pderiv i (momPoly i p)
      = C (-Complex.I) * (pderiv i (pderiv i p) - C (1 / 2 : ℂ) * (p + X i * pderiv i p)) := by
    rw [momPoly_apply, MvPolynomial.pderiv_C_mul, map_sub, MvPolynomial.pderiv_C_mul, hL]
  have hII : (C (-Complex.I) : MvPolynomial (Fin 3) ℂ) * C (-Complex.I) = -1 := by
    rw [← map_mul]
    norm_num
  have hhalf : (C (1 / 2 : ℂ) : MvPolynomial (Fin 3) ℂ) * C (1 / 2 : ℂ) = C (1 / 4 : ℂ) := by
    rw [← map_mul]
    norm_num
  have hone : (C (1 / 2 : ℂ) : MvPolynomial (Fin 3) ℂ) + C (1 / 2 : ℂ) = 1 := by
    rw [← map_add]
    norm_num
  have hexp : momPoly i (momPoly i p)
      = -(pderiv i (pderiv i p)) + C (1 / 2 : ℂ) * p + X i * pderiv i p
        - C (1 / 4 : ℂ) * (X i * (X i * p)) := by
    conv_lhs => rw [momPoly_apply]
    rw [hd]
    conv_lhs => rw [momPoly_apply]
    have hfac : C (-Complex.I) * (C (-Complex.I)
          * (pderiv i (pderiv i p) - C (1 / 2 : ℂ) * (p + X i * pderiv i p))
        - C (1 / 2 : ℂ) * (X i * (C (-Complex.I)
          * (pderiv i p - C (1 / 2 : ℂ) * (X i * p)))))
        = (C (-Complex.I) * C (-Complex.I))
          * ((pderiv i (pderiv i p) - C (1 / 2 : ℂ) * (p + X i * pderiv i p))
            - C (1 / 2 : ℂ) * (X i * (pderiv i p - C (1 / 2 : ℂ) * (X i * p)))) := by
      ring
    rw [hfac, hII]
    linear_combination (X i * pderiv i p) * hone - (X i * (X i * p)) * hhalf
  rw [hexp]
  simp only [crePoly_apply, annPoly_apply, mulXPoly_apply, MvPolynomial.smul_eq_C_mul]
  ring

#print axioms solution
