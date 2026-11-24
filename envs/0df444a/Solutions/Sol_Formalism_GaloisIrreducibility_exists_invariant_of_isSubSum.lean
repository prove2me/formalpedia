-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.exists_invariant_of_isSubSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:57.128124+00:00
-- url     : https://prove2.me/submissions/bb861f87-4444-4f22-aeef-2986555f82b5

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PermSubSumInv
import Theorems.Thm_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs_stable
import Theorems.Thm_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs_pd
import Theorems.Thm_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs_parts
import Theorems.Thm_Formalism_GaloisIrreducibility_SubsetSumInvariance_exists_le_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open SubsetSumInvariance
namespace Formalism.GaloisIrreducibility
theorem _root_.solution {α : Type} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (a : ℕ)
    (h : IsSubSum σ.partition.parts a) : ∃ A : Finset α, (∀ x ∈ A, σ x ∈ A) ∧ A.card = a := by
  obtain ⟨s, hs, hsum⟩ := h
  rw [← orbs_parts] at hs
  obtain ⟨t, ht, htf⟩ := exists_le_map Finset.card _ s hs
  let T : Finset (Finset α) := ⟨t, Multiset.nodup_of_le ht (orbs σ).nodup⟩
  have hT : T ⊆ orbs σ := fun O hO => Multiset.subset_of_le ht hO
  refine ⟨T.biUnion id, ?_, ?_⟩
  · intro x hx
    obtain ⟨O, hO, hxO⟩ := Finset.mem_biUnion.1 hx
    exact Finset.mem_biUnion.2 ⟨O, hO, orbs_stable (hT hO) x hxO⟩
  · rw [Finset.card_biUnion (fun O hO O' hO' hne => orbs_pd σ (hT hO) (hT hO') hne),
      Finset.sum_eq_multiset_sum]
    change (t.map fun O => (id O).card).sum = a
    simpa [htf] using hsum
end Formalism.GaloisIrreducibility
