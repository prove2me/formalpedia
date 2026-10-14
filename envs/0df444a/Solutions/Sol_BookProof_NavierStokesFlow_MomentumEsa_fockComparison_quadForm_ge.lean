-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumEsa.fockComparison_quadForm_ge
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:41:07.906772+00:00
-- url     : https://prove2.me/submissions/4a8d766b-8069-4923-9dbc-10cafb3d5f21

-- Generated from ChapterNavierStokesMomentumEsa.lean — solution of BookProof.NavierStokesFlow.MomentumEsa.fockComparison_quadForm_ge
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_fockSymbol_ge_one
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_diagMax_quadForm_ge_norm_sq
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa





open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ → ℝ) (hn : ∀ k, 0 ≤ n k)
    (x : maxDom (fockSymbol n)) :
    ‖(x : L2I Config)‖ ^ 2 ≤ quadForm (diagMax (fockSymbol n)) x := diagMax_quadForm_ge_norm_sq _ (fockSymbol_ge_one n hn) x
