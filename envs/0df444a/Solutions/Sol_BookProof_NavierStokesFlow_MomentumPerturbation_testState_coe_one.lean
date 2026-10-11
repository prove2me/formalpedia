-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumPerturbation.testState_coe_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:41:41.155745+00:00
-- url     : https://prove2.me/submissions/795e0091-e9a2-4764-91ec-d37a978623d9

-- Generated from ChapterNavierStokesMomentumPerturbation.lean — solution of BookProof.NavierStokesFlow.MomentumPerturbation.testState_coe_one
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumPerturbation
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumPerturbation





open LpNat BookProof.FarisLavine IkebeKato

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution : (testState : ℕ → ℂ) 1 = Complex.I := by

  simp [testState, lp.single_apply]
