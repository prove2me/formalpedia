-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:19:20.142813+00:00
-- url     : https://prove2.me/submissions/aee890f6-4173-4a28-8ead-2bc6e26308ea

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexAdditive
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_relLen_inf
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_relLen_ne_top_of_le
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_isLat_inf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TW
open Formalism.IrreducibleCountingLemmas.TW.Idx
variable {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V]
variable [FiniteDimensional K V]
namespace Formalism.IrreducibleCountingLemmas.TW.Idx
theorem _root_.solution {M N : Submodule O V} (hM : IsLat O K M) (hN : IsLat O K N) :
    relLen M N ≠ ⊤ := by
  rw [← relLen_inf]
  exact relLen_ne_top_of_le hM (isLat_inf hM hN) inf_le_left
end Formalism.IrreducibleCountingLemmas.TW.Idx
