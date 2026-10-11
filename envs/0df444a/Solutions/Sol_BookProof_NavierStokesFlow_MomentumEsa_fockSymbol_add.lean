-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumEsa.fockSymbol_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:39:31.039499+00:00
-- url     : https://prove2.me/submissions/208137cd-895c-41e5-bf53-2ce4517efb45

-- Generated from ChapterNavierStokesMomentumEsa.lean — solution of BookProof.NavierStokesFlow.MomentumEsa.fockSymbol_add
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa





open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ → ℝ) (a b : Config) :
    fockSymbol n (a + b) + 1 = fockSymbol n a + fockSymbol n b := by

  have hsum : (Finsupp.sum (a + b) fun k m => (m : ℝ) * n k)
      = (Finsupp.sum a fun k m => (m : ℝ) * n k) + Finsupp.sum b fun k m => (m : ℝ) * n k :=
    Finsupp.sum_add_index' (fun k => by simp) (fun k m₁ m₂ => by push_cast; ring)
  simp only [fockSymbol]
  rw [hsum]
  ring
