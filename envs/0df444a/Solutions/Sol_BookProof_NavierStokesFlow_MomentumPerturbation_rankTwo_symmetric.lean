-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumPerturbation.rankTwo_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:09:21.223993+00:00
-- url     : https://prove2.me/submissions/738428c7-98a0-4aa5-a419-64b9adc06f6a

-- Generated from ChapterNavierStokesMomentumPerturbation.lean — solution of BookProof.NavierStokesFlow.MomentumPerturbation.rankTwo_symmetric
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumPerturbation
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumPerturbation





open LpNat BookProof.FarisLavine IkebeKato

variable {ι : Type*}

variable {ι : Type*}


@[simp] private theorem rankTwo_apply (u w : L2I ι) (x : L2I ι) :
    rankTwo u w x = (inner ℂ u x : ℂ) • w + (inner ℂ w x : ℂ) • u := rfl

set_option maxHeartbeats 1000000 in
theorem solution (u w x y : L2I ι) :
    (inner ℂ (rankTwo u w x) y : ℂ) = inner ℂ x (rankTwo u w y) := by

  simp only [rankTwo_apply, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  rw [inner_conj_symm, inner_conj_symm]
  ring
