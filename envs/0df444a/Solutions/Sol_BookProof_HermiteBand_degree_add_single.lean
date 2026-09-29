-- Prove2me | solution 1 for BookProof.HermiteBand.degree_add_single
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-17T12:05:02.425815+00:00
-- url     : https://prove2.me/submissions/05dec573-218e-4ecc-951c-ff1d773337a2

-- Generated from ChapterHermiteBandCalculus.lean — solution of BookProof.HermiteBand.degree_add_single
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteBand








noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (α : Fin d →₀ ℕ) (i : Fin d) :
    (α + Finsupp.single i 1).degree = α.degree + 1 := by

  simp
