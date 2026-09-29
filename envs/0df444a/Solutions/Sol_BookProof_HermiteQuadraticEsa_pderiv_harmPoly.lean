-- Prove2me | solution 1 for BookProof.HermiteQuadraticEsa.pderiv_harmPoly
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:01:39.774684+00:00
-- url     : https://prove2.me/submissions/51826366-9dcc-4c7f-8ae6-14deacf1c223

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.pderiv_harmPoly
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem solution (j : Fin d) :
    pderiv j (harmPoly (d := d)) = C (1 / 2 : ℂ) * X j := by
  have hC : (C (1 / 4 : ℂ) : MvPolynomial (Fin d) ℂ) * 2 = C (1 / 2 : ℂ) := by
    have h2 : ((2 : MvPolynomial (Fin d) ℂ)) = C (2 : ℂ) :=
      (MvPolynomial.ext _ _ (congrFun rfl)).symm
    rw [h2, ← C_mul]
    norm_num
  unfold harmPoly
  rw [map_sum, Finset.sum_eq_single j]
  · rw [pderiv_C_mul, pow_two, pderiv_mul, pderiv_X_self]
    linear_combination (X j : MvPolynomial (Fin d) ℂ) * hC
  · intro k _ hk
    rw [pderiv_C_mul, pow_two, pderiv_mul, pderiv_X_of_ne hk]
    ring
  · intro h
    exact absurd (Finset.mem_univ j) h

#print axioms solution
