-- Prove2me | solution 2 for BookProof.NavierStokesFlow.AffineBlock.affBlockH_essentiallySelfAdjointOn_core
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:34:04.683114+00:00
-- url     : https://prove2.me/submissions/4630075d-9c7d-4be9-b6f3-bcf4a52b2f01

import Mathlib
import Definitions.Def_ChapterNavierStokesAffineBlockEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds
import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_PairShift_pairH_relative_bound
import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_PairShift_pairH_commForm_bound
import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_PairShift_pairH_symmetricOn
import Theorems.Thm_BookProof_NavierStokesFlow_AffineBlock_deficiencyTrivialAt_affBlockH
-- Generated from ChapterNavierStokesAffineBlockEsa.lean — theorem BookProof.NavierStokesFlow.AffineBlock.affBlockH_essentiallySelfAdjointOn_core
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineFiber.PairShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineBlock


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber BilinearEsa

variable {J : Type*}
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.AffineFiber BookProof.NavierStokesFlow.IkebeKato
  BookProof.FarisLavine in
theorem h43_pairH_esa {ι : Type*} (P : PairShift ι) :
    EssentiallySelfAdjointOn (lpFiniteModes ι)
      ((PairShift.pairH P).comp (Submodule.inclusion (finiteModes_le_maxDom P.sym))) :=
  essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds P.sym
    (fun k => le_trans zero_le_one (P.sym_ge_one k)) (PairShift.pairH P) 2 (32 * P.K ^ 2)
    (2 * P.step₁ * (1 / 4 + P.K) + 2 * P.step₂ * (1 / 4 + P.K))
    (PairShift.pairH_symmetricOn P)
    (by have := P.step₁_nonneg; have := P.step₂_nonneg; have := P.K_nonneg; positivity)
    (PairShift.pairH_relative_bound P) (PairShift.pairH_commForm_bound P)

theorem solution (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j)
    (hc : ∀ j, 0 ≤ c j) :
    EssentiallySelfAdjointOn (lpFiniteModes (ℕ × J)) (affBlockH κ c hκ hc) := by
  exact ⟨deficiencyTrivialAt_affBlockH κ c hκ hc _ fun j => (h43_pairH_esa (affData (hκ j) (hc j))).1,
    deficiencyTrivialAt_affBlockH κ c hκ hc _ fun j => (h43_pairH_esa (affData (hκ j) (hc j))).2⟩

