-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumPerturbation.exists_commForm_ne_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T19:53:51.37718+00:00
-- url     : https://prove2.me/submissions/a6f37257-6679-437b-a757-466f438d3ef4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterNavierStokesMomentumPerturbation.lean — solution of BookProof.NavierStokesFlow.MomentumPerturbation.exists_commForm_ne_zero
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumPerturbation
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumPerturbation_testState_mem_maxDom
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumPerturbation_commForm_witness_eq_neg_two
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumPerturbation





open LpNat BookProof.FarisLavine IkebeKato

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution :
    ∃ x : maxDom linSymbol,
      commForm (pertHam linSymbol (eState 0) (eState 1)) (diagMax linSymbol) x ≠ 0 := ⟨⟨testState, testState_mem_maxDom⟩, by rw [commForm_witness_eq_neg_two]; norm_num⟩
