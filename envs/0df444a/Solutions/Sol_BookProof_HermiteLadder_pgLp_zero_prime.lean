-- Prove2me | solution 1 for BookProof.HermiteLadder.pgLp_zero_prime
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:35:09.646122+00:00
-- url     : https://prove2.me/submissions/77da665c-602e-4542-b7cd-f1e206af3705

import Definitions.Def_ChapterHermiteProductCore
import Mathlib

open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

theorem solution : pgLp (0 : MvPolynomial (Fin d) ℂ) = 0 := by
  change pgMap (0 : MvPolynomial (Fin d) ℂ) = 0
  exact map_zero _
