-- Prove2me | solution 1 for BookProof.NavierStokesFlow.SignFlip.saffH_eq_affH_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T08:14:32.025691+00:00
-- url     : https://prove2.me/submissions/e198022e-1ab4-4d46-9acc-b157bbbc0303

-- Generated from ChapterNavierStokesSignFlip.lean — solution of BookProof.NavierStokesFlow.SignFlip.saffH_eq_affH_inc
import Mathlib
import Definitions.Def_ChapterNavierStokesSignFlip
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignFlip



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber
open BookProof.NavierStokesFlow.AffineFiber.PairShift
open BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution {κ : ℝ} (hκ : 0 ≤ κ) {c : ℝ} (hc : 0 ≤ c) :
    saffH hκ c = affH hκ (abs_nonneg c) := by

  simp only [saffH, esgn_of_nonneg hc, one_smul]
  rfl
