-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.isIrreducible_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:06:03.161297+00:00
-- url     : https://prove2.me/submissions/3cc2abf6-c867-4c99-ba4c-fb682dd7fcd8

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdempotent

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
variable {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution [Nontrivial V] (ρ : Representation ℂ G V)
    (h : ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤) :
    ρ.IsIrreducible := by
  unfold Representation.IsIrreducible
  refine { exists_pair_ne := ⟨⊥, ⊤, fun heq => ?_⟩, eq_bot_or_eq_top := fun W => ?_ }
  · have h1 := congrArg Subrepresentation.toSubmodule heq
    exact bot_ne_top (show (⊥ : Submodule ℂ V) = ⊤ from h1)
  · obtain ⟨S, hS⟩ := W
    rcases h S (fun g x hx => hS g hx) with h1 | h1
    · left
      subst h1
      rfl
    · right
      subst h1
      rfl
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
