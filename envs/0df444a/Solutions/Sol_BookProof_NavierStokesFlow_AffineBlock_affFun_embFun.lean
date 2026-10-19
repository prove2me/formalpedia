-- Prove2me | solution 1 for BookProof.NavierStokesFlow.AffineBlock.affFun_embFun
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:23:42.301998+00:00
-- url     : https://prove2.me/submissions/45c26e30-bef7-4565-8551-68a6a50c5620

-- Generated from ChapterNavierStokesAffineBlockEsa.lean — solution of BookProof.NavierStokesFlow.AffineBlock.affFun_embFun
import Mathlib
import Definitions.Def_ChapterNavierStokesAffineBlockEsa
import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_hFun_zero
import Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_embFun_of_ne
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineBlock



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber BilinearEsa
open BookProof.NavierStokesFlow.AffineFiber.PairShift

variable {J : Type*}

variable {J : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ j, 0 ≤ c j)
    (j : J) (a : ℕ → ℂ) :
    affFun κ c hκ hc (embFun j a)
      = embFun j (fun n => (affData (hκ j) (hc j)).fst.hFun a n
          + (affData (hκ j) (hc j)).snd.hFun a n) := by

  funext p
  obtain ⟨m, j'⟩ := p
  by_cases hj : j' = j
  · subst hj
    simp only [affFun, embFun_self]
  · simp only [affFun, hFun_zero, add_zero, embFun_of_ne _ _ hj]
