-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumEsa.nsComparison_selfAdjoint_maxDom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:39:28.795016+00:00
-- url     : https://prove2.me/submissions/0462b6d0-8513-4161-a5fd-beffe7840180

-- Generated from ChapterNavierStokesMomentumEsa.lean — solution of BookProof.NavierStokesFlow.MomentumEsa.nsComparison_selfAdjoint_maxDom
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_nsSymbol_nonneg
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_diagMax_essentiallySelfAdjointOn
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa





open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (d : ℕ) (p q : Fin d → ℕ → ℝ) :
    EssentiallySelfAdjointOn (maxDom (nsSymbol d p q)) (diagMax (nsSymbol d p q)) := diagMax_essentiallySelfAdjointOn _ (nsSymbol_nonneg d p q)
