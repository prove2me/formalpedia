-- Prove2me | solution 1 for Configuration.enables_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:46:22.845823+00:00
-- url     : https://prove2.me/submissions/dd3fbbdf-d75d-4290-8f04-5ecbf55c174e

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_Family_Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Definitions.Def_EventStructures_Prime_Configuration
import Theorems.Thm_ConfFamily_Indep_symm


set_option autoImplicit true
variable {L : Type*} (es : PES L)
open Configuration
local infix:50 " ⊢ " => enables es
namespace Configuration
theorem _root_.solution {c : Set es.Event} {e : es.Event} (h : c ⊢ e) :
    isConf es (c ∪ {e}) := by
  obtain ⟨⟨hConflictFree, hDownClosed⟩, hConsistent, hPast⟩ := h
  constructor
  · -- Conflict-free
    intro e₁ e₂ h₁ h₂
    obtain h₁ | h₁ := h₁
    · obtain h₂ | h₂ := h₂
      · exact hConflictFree h₁ h₂
      · rw [Set.mem_singleton_iff] at h₂
        rw [h₂]
        intro hConf
        exact hConsistent e₁ h₁ (es.conflict_symm.symm _ _ hConf)
    · rw [Set.mem_singleton_iff] at h₁
      obtain h₂ | h₂ := h₂
      · rw [h₁]
        intro hConf
        exact hConsistent e₂ h₂ hConf
      · rw [Set.mem_singleton_iff] at h₂
        rw [h₁, h₂]
        exact es.conflict_irrefl e
  · -- Downward closed
    intro e' e'' h' h''
    obtain h' | h' := h'
    · exact Set.mem_union_left _ (hDownClosed h' h'')
    · rw [Set.mem_singleton_iff] at h'
      subst h'
      rcases lt_or_eq_of_le h'' with hlt | rfl
      · exact Set.mem_union_left _ (hPast hlt)
      · exact Set.mem_union_right _ rfl
end Configuration
