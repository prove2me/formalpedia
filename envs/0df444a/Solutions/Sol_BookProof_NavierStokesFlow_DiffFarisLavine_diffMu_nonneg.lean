-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DiffFarisLavine.diffMu_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:05:56.290838+00:00
-- url     : https://prove2.me/submissions/9f8edd5f-4453-4389-8ed5-748d5b89c71b

-- Adapted from Leonardo Pedro, timepiece commit 61595bc, Apache-2.0.
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDiffFarisLavine.lean
import Definitions.Def_ChapterNavierStokesDiffFarisLavine
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 4000000
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.DiffFarisLavine
open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine
open BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.DifferentialL2

theorem solution (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ) :
    0 ≤ diffMu A c := by
  unfold diffMu velMu
  positivity

#print axioms solution
