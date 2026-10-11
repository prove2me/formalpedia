-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumEsa.fockComparison_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:41:22.452882+00:00
-- url     : https://prove2.me/submissions/a74897b2-537d-4849-b62c-413d308418fd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterNavierStokesMomentumEsa.lean — solution of BookProof.NavierStokesFlow.MomentumEsa.fockComparison_core
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_exists_finiteModes_graph_approx
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa





open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ → ℝ) (x : maxDom (fockSymbol n)) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : maxDom (fockSymbol n), (y : L2I Config) ∈ lpFiniteModes Config ∧
      ‖(y : L2I Config) - (x : L2I Config)‖ < ε ∧
        ‖diagMax (fockSymbol n) y - diagMax (fockSymbol n) x‖ < ε := exists_finiteModes_graph_approx _ x ε hε
