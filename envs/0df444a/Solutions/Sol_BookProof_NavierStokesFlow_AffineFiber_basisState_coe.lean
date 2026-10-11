-- Prove2me | solution 1 for BookProof.NavierStokesFlow.AffineFiber.basisState_coe
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:05:42.181184+00:00
-- url     : https://prove2.me/submissions/bf31256b-94df-47dd-a872-159dfcb1f24f

-- Generated from ChapterNavierStokesAffineFiberEsa.lean — solution of BookProof.NavierStokesFlow.AffineFiber.basisState_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineFiber



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian

variable {ι : Type*}

variable {ι : Type*}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable (P : PairShift ι)

set_option maxHeartbeats 1000000 in
theorem solution (κ c : ℝ) (n m : ℕ) :
    ((basisState κ c n : L2I ℕ) : ℕ → ℂ) m = if m = n then 1 else 0 := by

  simp [basisState, lp.single_apply, Pi.single_apply, eq_comm]
