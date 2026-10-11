-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumPerturbation.norm_eState
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:41:55.709601+00:00
-- url     : https://prove2.me/submissions/603a9f5f-36d4-428a-bc3d-6d0b7c42a088

-- Generated from ChapterNavierStokesMomentumPerturbation.lean — solution of BookProof.NavierStokesFlow.MomentumPerturbation.norm_eState
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumPerturbation
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumPerturbation





open LpNat BookProof.FarisLavine IkebeKato

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) : ‖eState k‖ = 1 := by

  have h : ‖(eState k : L2I ℕ)‖ = ‖(1 : ℂ)‖ := lp.norm_single (by norm_num) k 1
  simpa using h
