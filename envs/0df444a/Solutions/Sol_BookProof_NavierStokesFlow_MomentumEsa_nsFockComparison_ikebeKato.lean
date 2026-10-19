-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumEsa.nsFockComparison_ikebeKato
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T19:53:47.299114+00:00
-- url     : https://prove2.me/submissions/f9417eb2-ad36-4b3f-bfd7-d8b5f01b6045

-- Generated from ChapterNavierStokesMomentumEsa.lean — solution of BookProof.NavierStokesFlow.MomentumEsa.nsFockComparison_ikebeKato
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_nsSymbol_nonneg
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_fockComparison_ikebeKato
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa





open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa
open BookProof.NavierStokesGaugeY

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (d : ℕ) (p q : Fin d → ℕ → ℝ) :
    EssentiallySelfAdjointOn (lpFiniteModes Config)
      ((diagMax (nsFockSymbol d p q)).comp
        (Submodule.inclusion (finiteModes_le_maxDom (nsFockSymbol d p q)))) := fockComparison_ikebeKato _ (nsSymbol_nonneg d p q)
