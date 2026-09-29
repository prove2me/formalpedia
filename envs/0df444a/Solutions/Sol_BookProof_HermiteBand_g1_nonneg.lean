-- Prove2me | solution 1 for BookProof.HermiteBand.g1_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-17T12:05:05.633061+00:00
-- url     : https://prove2.me/submissions/b4dad882-d3cb-4ddc-97ad-4320fcc0b9f3

-- Generated from ChapterHermiteBandCalculus.lean — solution of BookProof.HermiteBand.g1_nonneg
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteBand








noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) : 0 ≤ g1 n := Real.sqrt_nonneg _
