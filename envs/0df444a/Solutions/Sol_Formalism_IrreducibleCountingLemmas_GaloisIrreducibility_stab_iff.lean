-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.stab_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:52:03.951814+00:00
-- url     : https://prove2.me/submissions/a1fb88b7-d4c2-4b51-a882-49d5300ad2e1

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaP

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
variable {N : ℕ}
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (A : Finset (Fin N)) (σ : Equiv.Perm (Fin N)) (h : ∀ x ∈ A, σ x ∈ A) (x : Fin N) :
    σ x ∈ A ↔ x ∈ A := by
  constructor
  · intro hx
    by_contra hxA
    have hsub : A.image σ ⊆ A := fun y hy => by
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      exact h z hz
    have hcard : (A.image σ).card = A.card := Finset.card_image_of_injective A σ.injective
    have heq := Finset.eq_of_subset_of_card_le hsub hcard.ge
    rw [← heq] at hx
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hx
    exact hxA (σ.injective hzx ▸ hz)
  · exact h x
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
