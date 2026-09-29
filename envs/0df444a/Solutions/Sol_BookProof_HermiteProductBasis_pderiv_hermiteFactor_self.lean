-- Prove2me | solution 1 for BookProof.HermiteProductBasis.pderiv_hermiteFactor_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:30:15.807852+00:00
-- url     : https://prove2.me/submissions/d39de9f0-a814-4e88-929c-89153847af2a

-- Generated from ChapterHermiteProductBasis.lean — solution of BookProof.HermiteProductBasis.pderiv_hermiteFactor_self
import Mathlib
import Definitions.Def_ChapterHermiteProductBasis
import Theorems.Thm_BookProof_HermiteProductBasis_pderiv_aeval_self
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteProductBasis








open MeasureTheory MvPolynomial BookProof.HermiteCore BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (n : ℕ) :
    pderiv i (hermiteFactor i n) = (n : ℂ) • hermiteFactor i (n - 1) := by

  cases n with
  | zero => simp [hermiteFactor, hermiteCx_zero]
  | succ m =>
      rw [hermiteFactor, pderiv_aeval_self]
      have h : Polynomial.derivative (hermiteCx (m + 1)) = ((m : ℂ) + 1) • hermiteCx m := by
        have hm := congrArg (Polynomial.map (Int.castRingHom ℂ)) (derivative_hermiteZ m)
        simpa [hermiteCx, Polynomial.derivative_map, Polynomial.smul_eq_C_mul,
          Polynomial.map_mul] using hm
      rw [h]
      simp [hermiteFactor, map_smul]
