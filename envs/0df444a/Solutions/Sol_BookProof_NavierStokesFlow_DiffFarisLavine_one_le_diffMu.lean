-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DiffFarisLavine.one_le_diffMu
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:05:57.051016+00:00
-- url     : https://prove2.me/submissions/f7f78f7a-9551-4cd6-a35b-e65e471257a2

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
    1 ≤ diffMu A c := by
  unfold diffMu velMu
  have h1 : 0 ≤ ∑ i, ∑ k, |A i k| := by positivity
  have h2 : 0 ≤ ∑ i, |seqConst c i| := by positivity
  linarith

#print axioms solution
