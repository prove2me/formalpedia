-- Prove2me | solution 1 for BookProof.HermiteLadder.pgLp_smul_prime
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:48:06.70219+00:00
-- url     : https://prove2.me/submissions/78dcb213-0abc-481b-a617-b691654ad6d0

import Definitions.Def_ChapterHermiteProductCore

open BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

theorem solution (c : ℂ) (p : MvPolynomial (Fin d) ℂ) : pgLp (c • p) = c • pgLp p := by
  change (pgMap (d := d)) (c • p) = c • (pgMap (d := d)) p
  exact (pgMap (d := d)).map_smul c p
