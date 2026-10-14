-- Prove2me | solution 1 for BookProof.NavierStokesFlow.IkebeKato.diagMax_quadForm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T13:16:50.148679+00:00
-- url     : https://prove2.me/submissions/a10f479d-b247-43ec-ac09-e0db9f15a9ff

-- Generated from ChapterNavierStokesIkebeKato.lean — solution of BookProof.NavierStokesFlow.IkebeKato.diagMax_quadForm_nonneg
import Mathlib
import Definitions.Def_ChapterNavierStokesIkebeKato
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_diagMax_hasSum_quadForm
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.IkebeKato



open scoped ENNReal



open LpNat BookProof.FarisLavine

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) (x : maxDom c) :
    0 ≤ quadForm (diagMax c) x := by

  refine (diagMax_hasSum_quadForm c x).nonneg fun k => ?_
  exact mul_nonneg (hc k) (sq_nonneg _)
