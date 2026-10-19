-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumEsa.fockComparison_ikebeKato
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T19:27:03.918358+00:00
-- url     : https://prove2.me/submissions/91950ffd-04e0-4ae2-bf3f-69d49fb8cb76

-- Generated from ChapterNavierStokesMomentumEsa.lean — solution of BookProof.NavierStokesFlow.MomentumEsa.fockComparison_ikebeKato
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_fockSymbol_nonneg
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_ikebeKato_momentum
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa





open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ → ℝ) (hn : ∀ k, 0 ≤ n k) :
    EssentiallySelfAdjointOn (lpFiniteModes Config)
      ((diagMax (fockSymbol n)).comp
        (Submodule.inclusion (finiteModes_le_maxDom (fockSymbol n)))) := ikebeKato_momentum _ (fockSymbol_nonneg n hn)
