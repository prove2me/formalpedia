-- Prove2me | solution 1 for BookProof.NavierStokesFlow.BilinearEsa.blockVec_bilH
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-03T14:57:58.173867+00:00
-- url     : https://prove2.me/submissions/c73c4ab1-a2e2-4734-98d4-f1b10d23b42d

-- Generated from ChapterNavierStokesBilinearEsa.lean — solution of BookProof.NavierStokesFlow.BilinearEsa.blockVec_bilH
import Mathlib
import Definitions.Def_ChapterNavierStokesBilinearEsa
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_blockVec_mem_maxDom
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.BilinearEsa



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine

variable {J : Type*}

variable {J : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (κ : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (v : lpFiniteModes (ℕ × J)) (j : J) :
    blockVec ((bilH κ v : L2I (ℕ × J))) j
      = nsH (κ j) (hκ j) ⟨blockVec ((v : L2I (ℕ × J))) j, blockVec_mem_maxDom κ v j⟩ := lp.ext (funext fun _ => rfl)
