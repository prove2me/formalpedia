-- Prove2me | solution 1 for BookProof.HermiteBand.g2_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-17T12:05:06.938794+00:00
-- url     : https://prove2.me/submissions/8652833e-4ec6-437a-b9d5-6429a1081ff2

-- Generated from ChapterHermiteBandCalculus.lean — solution of BookProof.HermiteBand.g2_nonneg
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteBand








noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

























open BookProof.NavierStokesFlow.DifferentialL2

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) : 0 ≤ g2 n := by

  simp only [g2]
  positivity
