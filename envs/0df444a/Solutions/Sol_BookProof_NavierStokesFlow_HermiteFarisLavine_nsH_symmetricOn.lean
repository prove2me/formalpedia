-- Prove2me | solution 1 for BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:39:17.571999+00:00
-- url     : https://prove2.me/submissions/6ad66b2a-531b-4616-bcb5-bfd5de593d86

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — solution of BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_symmetricOn
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_hasSum_inner_nsH_left
import Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_hasSum_inner_nsH_right
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}

set_option maxHeartbeats 1000000 in
theorem solution (hκ : 0 ≤ κ) : SymmetricOn (maxDom (oscSymbol κ)) (nsH κ hκ) := by

  intro x y
  exact (hasSum_inner_nsH_left hκ x (y : L2I ℕ)).unique (hasSum_inner_nsH_right hκ x y)
