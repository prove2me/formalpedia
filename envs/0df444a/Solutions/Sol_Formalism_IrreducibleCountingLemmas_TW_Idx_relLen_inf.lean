-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:22.510377+00:00
-- url     : https://prove2.me/submissions/056cbe38-4a0c-40dc-88de-22dbf7bfe47c

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
variable {O V : Type} [CommRing O] [AddCommGroup V] [Module O V]
namespace Formalism.IrreducibleCountingLemmas.TW.Idx
theorem _root_.solution (M N : Submodule O V) : relLen M (M ⊓ N) = relLen M N := by
  unfold relLen
  have : (M ⊓ N).comap M.subtype = N.comap M.subtype := by
    ext x; simp
  rw [this]
end Formalism.IrreducibleCountingLemmas.TW.Idx
