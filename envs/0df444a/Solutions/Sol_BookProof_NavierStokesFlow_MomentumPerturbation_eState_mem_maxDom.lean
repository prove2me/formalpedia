-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumPerturbation.eState_mem_maxDom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T12:09:06.802153+00:00
-- url     : https://prove2.me/submissions/2aa503b9-8877-4884-8792-2dd221fbb5a4

-- Generated from ChapterNavierStokesMomentumPerturbation.lean — solution of BookProof.NavierStokesFlow.MomentumPerturbation.eState_mem_maxDom
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumPerturbation
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumPerturbation





open LpNat BookProof.FarisLavine IkebeKato

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) : eState k ∈ maxDom linSymbol := finiteModes_le_maxDom linSymbol (lpSingle_mem_lpFiniteModes k (1 : ℂ))
