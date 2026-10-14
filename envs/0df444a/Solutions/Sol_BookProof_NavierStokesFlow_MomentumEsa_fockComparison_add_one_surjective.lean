-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumEsa.fockComparison_add_one_surjective
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:39:34.176784+00:00
-- url     : https://prove2.me/submissions/5cb4d50d-fb82-4739-89ba-085469002cf6

-- Generated from ChapterNavierStokesMomentumEsa.lean — solution of BookProof.NavierStokesFlow.MomentumEsa.fockComparison_add_one_surjective
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_fockSymbol_nonneg
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_diagMax_add_one_surjective
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa





open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ → ℝ) (hn : ∀ k, 0 ≤ n k) (f : L2I Config) :
    ∃ x : maxDom (fockSymbol n), (diagMax (fockSymbol n) x : L2I Config) + (x : L2I Config) = f := diagMax_add_one_surjective _ (fockSymbol_nonneg n hn) f
