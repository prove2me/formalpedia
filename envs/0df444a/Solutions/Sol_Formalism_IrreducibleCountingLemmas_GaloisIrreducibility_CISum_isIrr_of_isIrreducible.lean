-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.CISum.isIrr_of_isIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:52.502054+00:00
-- url     : https://prove2.me/submissions/ccfb9f1e-c7da-40b1-9060-268553f000f4

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdempotent
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CentralIdempotentsSumOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.CISum
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.CISum
theorem _root_.solution {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : IsIrr ρ := by
  unfold Representation.IsIrreducible at h
  refine ⟨?_, fun W hW => ?_⟩
  · by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤) (Subrepresentation.ext (Subsingleton.elim _ _))
  · rcases h.eq_bot_or_eq_top ⟨W, fun g v hv => hW g v hv⟩ with h1 | h1
    · left
      exact congrArg Subrepresentation.toSubmodule h1
    · right
      exact congrArg Subrepresentation.toSubmodule h1
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.CISum
