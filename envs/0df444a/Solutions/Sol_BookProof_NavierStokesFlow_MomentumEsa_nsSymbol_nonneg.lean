-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumEsa.nsSymbol_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:39:27.637077+00:00
-- url     : https://prove2.me/submissions/1444256f-bf48-45b0-8b28-ad977c1082b6

-- Generated from ChapterNavierStokesMomentumEsa.lean — solution of BookProof.NavierStokesFlow.MomentumEsa.nsSymbol_nonneg
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_nsSymbol_ge_one
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa





open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (d : ℕ) (p q : Fin d → ℕ → ℝ) (k : ℕ) : 0 ≤ nsSymbol d p q k := le_trans zero_le_one (nsSymbol_ge_one d p q k)
