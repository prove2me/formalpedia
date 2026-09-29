-- Prove2me | solution 1 for BookProof.HermiteProductBasis.crePoly_hermiteMv
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T13:20:41.276093+00:00
-- url     : https://prove2.me/submissions/d47f0776-bb79-4198-bca2-553aec9e1aba

-- Generated from ChapterHermiteProductBasis.lean — solution of BookProof.HermiteProductBasis.crePoly_hermiteMv
import Mathlib
import Definitions.Def_ChapterHermiteProductBasis
import Theorems.Thm_BookProof_HermiteProductBasis_pderiv_hermiteMv
import Theorems.Thm_BookProof_HermiteProductBasis_crePoly_apply
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteProductBasis








open MeasureTheory MvPolynomial BookProof.HermiteCore BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (a : Fin d →₀ ℕ) :
    crePoly i (hermiteMv a) = hermiteMv (a + Finsupp.single i 1) := by

  rw [crePoly_apply, hermiteMv_X_mul, pderiv_hermiteMv]
  abel
