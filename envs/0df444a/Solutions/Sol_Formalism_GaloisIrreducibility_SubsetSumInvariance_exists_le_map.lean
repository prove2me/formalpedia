-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.SubsetSumInvariance.exists_le_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:25:52.789685+00:00
-- url     : https://prove2.me/submissions/78cea688-c79f-4f99-8c70-afdf60ca4f7a

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PermSubSumInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Formalism.GaloisIrreducibility.SubsetSumInvariance
namespace Formalism.GaloisIrreducibility.SubsetSumInvariance
theorem _root_.solution {β γ : Type*} (f : β → γ) (m : Multiset β) :
    ∀ s : Multiset γ, s ≤ m.map f → ∃ t ≤ m, t.map f = s := by
  classical
  induction m using Multiset.induction_on with
  | empty =>
    intro s hs
    refine ⟨0, le_rfl, ?_⟩
    simp only [Multiset.map_zero, nonpos_iff_eq_zero] at hs ⊢
    exact hs.symm
  | cons b m ih =>
    intro s hs
    rw [Multiset.map_cons] at hs
    by_cases hb : f b ∈ s
    · have hle : s.erase (f b) ≤ m.map f := by
        have := Multiset.erase_le_erase (f b) hs
        rwa [Multiset.erase_cons_head] at this
      obtain ⟨t, ht, htf⟩ := ih _ hle
      refine ⟨b ::ₘ t, Multiset.cons_le_cons b ht, ?_⟩
      rw [Multiset.map_cons, htf, Multiset.cons_erase hb]
    · obtain ⟨t, ht, htf⟩ := ih s ((Multiset.le_cons_of_notMem hb).1 hs)
      exact ⟨t, ht.trans (Multiset.le_cons_self _ _), htf⟩
end Formalism.GaloisIrreducibility.SubsetSumInvariance
