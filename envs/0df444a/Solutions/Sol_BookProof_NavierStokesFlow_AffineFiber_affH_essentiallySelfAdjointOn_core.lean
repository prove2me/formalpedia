-- Prove2me | solution 1 for BookProof.NavierStokesFlow.AffineFiber.affH_essentiallySelfAdjointOn_core
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:33:50.51569+00:00
-- url     : https://prove2.me/submissions/c1a7ed3d-c38e-48c2-a614-97b1acb71a01

import Mathlib
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds
import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_PairShift_pairH_relative_bound
import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_PairShift_pairH_commForm_bound
import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_PairShift_pairH_symmetricOn
-- Generated from ChapterNavierStokesAffineFiberEsa.lean — theorem BookProof.NavierStokesFlow.AffineFiber.affH_essentiallySelfAdjointOn_core
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineFiber


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian

variable {ι : Type*}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable (P : PairShift ι)
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

theorem solution {κ c : ℝ} (hκ : 0 ≤ κ) (hc : 0 ≤ c) :
    EssentiallySelfAdjointOn (lpFiniteModes ℕ)
      ((affH hκ hc).comp
        (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol (affMu κ c))))) := by
  exact h43_pairH_esa (affData hκ hc)

