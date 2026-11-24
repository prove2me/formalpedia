-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TW.Idx.isLat_of_isLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:52:06.070916+00:00
-- url     : https://prove2.me/submissions/2d7b36cc-a85f-4e52-8423-1f584628235e

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexAdditive

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
namespace Formalism.IrreducibleCountingLemmas.TW.Idx
theorem _root_.solution (M : Submodule O V) [Submodule.IsLattice K M] : IsLat O K M :=
  ⟨Submodule.IsLattice.fg, Submodule.IsLattice.span_eq_top⟩
end Formalism.IrreducibleCountingLemmas.TW.Idx
