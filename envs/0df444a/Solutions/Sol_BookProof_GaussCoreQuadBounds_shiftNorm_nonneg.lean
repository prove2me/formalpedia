-- Prove2me | solution 1 for BookProof.GaussCoreQuadBounds.shiftNorm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-12T13:03:01.988461+00:00
-- url     : https://prove2.me/submissions/54528eaa-55e6-4c86-86d3-332a9a06dc20

import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds
open Finset MvPolynomial

noncomputable section
variable {D : ℕ}

theorem solution (p : MvPolynomial (Fin D) ℂ) : 0 ≤ shiftNorm p :=
  norm_nonneg _
