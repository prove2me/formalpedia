-- Prove2me | solution 1 for BookProof.HermiteBand.le_degree
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-17T12:05:10.237744+00:00
-- url     : https://prove2.me/submissions/b3fa1faa-0d91-40fb-ad41-b56a36842c76

-- Generated from ChapterHermiteBandCalculus.lean — solution of BookProof.HermiteBand.le_degree
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteBand








noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (α : Fin d →₀ ℕ) (i : Fin d) : α i ≤ α.degree := Finsupp.le_degree i α
