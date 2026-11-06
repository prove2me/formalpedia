-- Prove2me | solution 1 for BookProof.HermiteLadder.pgLp_add_prime
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:40:33.414905+00:00
-- url     : https://prove2.me/submissions/ea3725cb-badf-4061-bd86-6792fe0169f4

import Definitions.Def_ChapterHermiteProductCore

open BookProof.HermiteProductCore
open MeasureTheory MvPolynomial
open scoped ENNReal

noncomputable section

variable {d : ℕ}

theorem solution (p q : MvPolynomial (Fin d) ℂ) : pgLp (p + q) = pgLp p + pgLp q := by
  change (pgMap (d := d)) (p + q) = (pgMap (d := d)) p + (pgMap (d := d)) q
  exact map_add pgMap p q
