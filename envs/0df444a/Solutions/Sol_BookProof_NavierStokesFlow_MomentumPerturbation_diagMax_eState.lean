-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumPerturbation.diagMax_eState
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T19:53:50.306867+00:00
-- url     : https://prove2.me/submissions/1353e589-3b7e-4899-82b7-5aadbf5fb9a0

-- Generated from ChapterNavierStokesMomentumPerturbation.lean — solution of BookProof.NavierStokesFlow.MomentumPerturbation.diagMax_eState
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumPerturbation
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumPerturbation_eState_mem_maxDom
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumPerturbation





open LpNat BookProof.FarisLavine IkebeKato

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) :
    (diagMax linSymbol ⟨eState k, eState_mem_maxDom k⟩ : L2I ℕ)
      = ((linSymbol k : ℂ)) • eState k := by

  classical
  refine lp.ext (funext fun j => ?_)
  rw [diagMax_coe]
  simp only [eState, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply, Pi.single_apply]
  by_cases hjk : j = k
  · subst hjk; simp
  · simp [hjk]
