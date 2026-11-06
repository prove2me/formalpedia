-- Prove2me | solution 1 for BookProof.HermiteLadder.hamPolyL_eq
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:54:39.921338+00:00
-- url     : https://prove2.me/submissions/18a9294f-1b10-4660-aa66-b45a131fa16b

import Definitions.Def_ChapterHermiteLadderOrder

open BookProof.QgHermiteFriedrichs
open BookProof.HermiteLadder
open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs BookProof.DegSchrodinger
open scoped ENNReal

noncomputable section

variable {d : ℕ}

theorem solution (S : Finset (Fin d)) (q : MvPolynomial (Fin d) ℂ) :
    hamPolyL S q = -(∑ j ∈ S, coreDL j ∘ₗ coreDL j) + mulL q := by
  ext p
  simp [hamPolyL, kinPolyS, coreDL, mulL]
