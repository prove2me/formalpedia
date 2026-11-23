-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:03:43.83629+00:00
-- url     : https://prove2.me/submissions/9bd2940e-036b-4db4-af53-11a6dfa6b4e7

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
theorem _root_.solution {M N : Submodule O V} (h : M ≤ N) : relLen M N = 0 := by
  unfold relLen
  have : N.comap M.subtype = ⊤ := by
    rw [eq_top_iff]; intro x _; exact h x.2
  rw [this]
  exact Module.length_eq_zero
end Formalism.IrreducibleCountingLemmas.TW.Idx
