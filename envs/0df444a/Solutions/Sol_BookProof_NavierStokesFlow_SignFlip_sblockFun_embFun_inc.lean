-- Prove2me | solution 1 for BookProof.NavierStokesFlow.SignFlip.sblockFun_embFun_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T08:19:50.012213+00:00
-- url     : https://prove2.me/submissions/750dbba8-c063-4b7e-9df1-553639dfa4df

-- Generated from ChapterNavierStokesSignFlip.lean — solution of BookProof.NavierStokesFlow.SignFlip.sblockFun_embFun_inc
import Mathlib
import Definitions.Def_ChapterNavierStokesSignFlip
import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_hFun_zero
import Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_embFun_of_ne
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesBilinearEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignFlip
open BookProof.NavierStokesFlow.BilinearEsa



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber
open BookProof.NavierStokesFlow.AffineFiber.PairShift

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {ι : Type*}
variable {J : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (j : J) (a : ℕ → ℂ) :
    sblockFun κ c hκ (embFun j a)
      = embFun j (fun n => (affData (hκ j) (abs_nonneg (c j))).fst.hFun a n
          + esgn (c j) * (affData (hκ j) (abs_nonneg (c j))).snd.hFun a n) := by

  funext q
  obtain ⟨m, j'⟩ := q
  by_cases hj : j' = j
  · subst hj
    simp only [sblockFun, embFun_self]
  · simp only [sblockFun, hFun_zero, mul_zero, add_zero, embFun_of_ne _ _ hj]
