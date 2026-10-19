-- Prove2me | solution 1 for BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_essentiallySelfAdjointOn_core
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T19:53:44.096751+00:00
-- url     : https://prove2.me/submissions/7909d91a-2f95-44e2-aa38-c50cb56655a7

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — solution of BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_nsH_symmetricOn
import Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_nsH_relative_bound
import Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_nsH_commForm_bound
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}

set_option maxHeartbeats 1000000 in
theorem solution (hκ : 0 ≤ κ) :
    EssentiallySelfAdjointOn (lpFiniteModes ℕ)
      ((nsH κ hκ).comp (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol κ)))) :=
  essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds (oscSymbol κ)
      (oscSymbol_nonneg hκ) (nsH κ hκ) (1 / 2) (2 * κ ^ 2) (2 * κ + 4 * κ ^ 2)
      (nsH_symmetricOn hκ) (by positivity) (nsH_relative_bound hκ) (nsH_commForm_bound hκ)
