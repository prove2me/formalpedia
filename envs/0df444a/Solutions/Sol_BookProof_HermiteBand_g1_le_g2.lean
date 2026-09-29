-- Prove2me | solution 1 for BookProof.HermiteBand.g1_le_g2
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-17T12:05:04.338598+00:00
-- url     : https://prove2.me/submissions/db43a501-32e7-4ca0-8613-3a2a6040af39

-- Generated from ChapterHermiteBandCalculus.lean — solution of BookProof.HermiteBand.g1_le_g2
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteBand








noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) : g1 n ≤ g2 n := by

  have hsq : Real.sqrt ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ (n : ℝ) + 1 by positivity),
      Real.sqrt_nonneg ((n : ℝ) + 1),
      sq_nonneg (Real.sqrt ((n : ℝ) + 1) - 1)]
  simpa [g1, g2] using hsq
