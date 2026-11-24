-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TW.Idx.isLat_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:59:39.877596+00:00
-- url     : https://prove2.me/submissions/c0328331-659f-4d46-a1bc-107d2dbcde5f

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexAdditive
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_isLattice_of_isLat
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_isLat_of_isLattice

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
    IsLat O K (M ⊓ N) := by
  have := isLattice_of_isLat hM
  have := isLattice_of_isLat hN
  exact isLat_of_isLattice _
end Formalism.IrreducibleCountingLemmas.TW.Idx
