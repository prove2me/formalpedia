-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumEsa.nsComparison_quadForm_ge
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:39:29.984479+00:00
-- url     : https://prove2.me/submissions/ffc8436c-cecd-4325-82b0-cbd4b74bf153

-- Generated from ChapterNavierStokesMomentumEsa.lean — solution of BookProof.NavierStokesFlow.MomentumEsa.nsComparison_quadForm_ge
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_nsSymbol_ge_one
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_diagMax_quadForm_ge_norm_sq
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa





open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (d : ℕ) (p q : Fin d → ℕ → ℝ)
    (x : maxDom (nsSymbol d p q)) :
    ‖(x : L2I ℕ)‖ ^ 2 ≤ quadForm (diagMax (nsSymbol d p q)) x := diagMax_quadForm_ge_norm_sq _ (nsSymbol_ge_one d p q) x
