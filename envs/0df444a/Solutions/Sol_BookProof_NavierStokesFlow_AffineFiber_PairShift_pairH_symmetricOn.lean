-- Prove2me | solution 1 for BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T02:42:07.485887+00:00
-- url     : https://prove2.me/submissions/601fb29b-be93-4bf3-a618-aae570cbf191

-- Generated from ChapterNavierStokesAffineFiberEsa.lean — solution of BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_symmetricOn
import Mathlib
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_PairShift_pairH_apply
import Theorems.Thm_BookProof_NavierStokesFlow_ShiftHamiltonian_ShiftData_shiftH_symmetricOn
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineFiber.PairShift



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian
open BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData
open BookProof.NavierStokesFlow.AffineFiber

variable {ι : Type*}

variable {ι : Type*}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable (P : PairShift ι)

set_option maxHeartbeats 1000000 in
theorem solution : SymmetricOn (maxDom P.sym) (pairH P) := by

  intro x y
  have h₁ : (inner ℂ (ShiftData.shiftH P.fst x : L2I ι) (y : L2I ι) : ℂ)
      = inner ℂ (x : L2I ι) (ShiftData.shiftH P.fst y : L2I ι) :=
    ShiftData.shiftH_symmetricOn P.fst x y
  have h₂ : (inner ℂ (ShiftData.shiftH P.snd x : L2I ι) (y : L2I ι) : ℂ)
      = inner ℂ (x : L2I ι) (ShiftData.shiftH P.snd y : L2I ι) :=
    ShiftData.shiftH_symmetricOn P.snd x y
  change (inner ℂ (pairH P x : L2I ι) (y : L2I ι) : ℂ) = inner ℂ (x : L2I ι) (pairH P y : L2I ι)
  rw [pairH_apply, pairH_apply, inner_add_left, inner_add_right, h₁, h₂]
