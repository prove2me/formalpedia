-- Prove2me | solution 1 for BookProof.HermiteQuadraticEsa.abs_coord_zero_le_norm_two
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:01:24.259861+00:00
-- url     : https://prove2.me/submissions/a03888a7-d826-4a0d-81e6-19e49a0120e9

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.abs_coord_zero_le_norm_two
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem solution (x : Vd 2) : |x 0| ≤ ‖x‖ := by
  have h : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by rw [norm_sq_eq_sum x, Fin.sum_univ_two]
  nlinarith [abs_nonneg (x 0), norm_nonneg x, sq_abs (x 0), sq_nonneg (x 1)]

#print axioms solution
