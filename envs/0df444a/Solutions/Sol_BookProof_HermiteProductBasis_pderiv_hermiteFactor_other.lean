-- Prove2me | solution 1 for BookProof.HermiteProductBasis.pderiv_hermiteFactor_other
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:30:15.024473+00:00
-- url     : https://prove2.me/submissions/d69d96bf-7c3b-45df-897c-58922109f84b

-- Generated from ChapterHermiteProductBasis.lean — solution of BookProof.HermiteProductBasis.pderiv_hermiteFactor_other
import Mathlib
import Definitions.Def_ChapterHermiteProductBasis
import Theorems.Thm_BookProof_HermiteProductBasis_pderiv_aeval_other
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteProductBasis








open MeasureTheory MvPolynomial BookProof.HermiteCore BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {i j : Fin d} (h : j ≠ i) (n : ℕ) :
    pderiv j (hermiteFactor i n) = 0 := pderiv_aeval_other h _
