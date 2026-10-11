-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumEsa.fockSymbol_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:39:32.104467+00:00
-- url     : https://prove2.me/submissions/26733209-e995-4b6b-9f20-90ef0a1e6209

-- Generated from ChapterNavierStokesMomentumEsa.lean — solution of BookProof.NavierStokesFlow.MomentumEsa.fockSymbol_ge_one
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa





open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ → ℝ) (hn : ∀ k, 0 ≤ n k) (a : Config) :
    1 ≤ fockSymbol n a := by

  have h : (0 : ℝ) ≤ a.sum fun k m => (m : ℝ) * n k :=
    Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg _) (hn k)
  simp only [fockSymbol]
  linarith
