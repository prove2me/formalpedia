-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumPerturbation.linSymbol_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:41:39.05249+00:00
-- url     : https://prove2.me/submissions/bd1d33de-49c5-4f64-89ed-1ac09fe2df46

-- Generated from ChapterNavierStokesMomentumPerturbation.lean — solution of BookProof.NavierStokesFlow.MomentumPerturbation.linSymbol_ge_one
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumPerturbation
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumPerturbation





open LpNat BookProof.FarisLavine IkebeKato

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) : 1 ≤ linSymbol k := by

  simp only [linSymbol]
  linarith [Nat.cast_nonneg (α := ℝ) k]
