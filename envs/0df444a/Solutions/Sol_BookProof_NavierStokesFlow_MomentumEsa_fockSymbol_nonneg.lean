-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumEsa.fockSymbol_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:39:33.181504+00:00
-- url     : https://prove2.me/submissions/58ae4d8b-52e1-44c6-b1ef-c4e6b2bfb6f1

-- Generated from ChapterNavierStokesMomentumEsa.lean — solution of BookProof.NavierStokesFlow.MomentumEsa.fockSymbol_nonneg
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_fockSymbol_ge_one
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa





open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ → ℝ) (hn : ∀ k, 0 ≤ n k) (a : Config) :
    0 ≤ fockSymbol n a := le_trans zero_le_one (fockSymbol_ge_one n hn a)
