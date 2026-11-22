-- Prove2me | solution 1 for ConfFamily.toLTSI_LPV
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:41:24.304266+00:00
-- url     : https://prove2.me/submissions/62055364-4b54-4ed6-8061-159c0ff5a294

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_Family_LTSI
import Theorems.Thm_Bisimilar_symm
import Theorems.Thm_ConfFamily_Indep_symm
import Theorems.Thm_ConfFamily_union_pair_comm


set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
open ConfFamily
namespace ConfFamily
theorem _root_.solution : LTSI.LPV (toLTSI F) where
  indep_step_left
    | ⟨e, _, h, hfr, _, hlbl, _, htgt, _⟩ => ⟨e, h.2.1, hfr, hlbl, htgt⟩
  indep_step_right
    | ⟨_, e, h, _, hfr, _, hlbl, _, htgt⟩ => ⟨e, h.2.2.1, hfr, hlbl, htgt⟩
  indep_irrefl := by
    rintro s a s' ⟨e₁, e₂, hind, hfr₁, -, -, -, htgt₁, htgt₂⟩
    refine hind.1 ?_
    have hset : s.val ∪ {e₁} = s.val ∪ {e₂} := htgt₁.symm.trans htgt₂
    rcases (hset ▸ Set.mem_union_right s.val (rfl : e₁ ∈ {e₁})) with h | h
    · exact (hfr₁ h).elim
    · exact h
  indep_symm
    | ⟨e₁, e₂, hind, f₁, f₂, l₁, l₂, t₁, t₂⟩ =>
      ⟨e₂, e₁, hind.symm, f₂, f₁, l₂, l₁, t₂, t₁⟩
  square := by
    rintro s a s₁ b s₂ ⟨e₁, e₂, hind, f₁, f₂, l₁, l₂, t₁, t₂⟩
    -- the closing state is `s ∪ {e₁} ∪ {e₂}`, which `Indep` already supplies
    have hu : F.Config (s.val ∪ {e₁} ∪ {e₂}) := hind.2.2.2
    refine ⟨⟨s.val ∪ {e₁} ∪ {e₂}, hu⟩, ⟨e₂, ⟨?_, ?_⟩, ?_, l₂, ?_⟩,
      ⟨e₁, ⟨?_, ?_⟩, ?_, l₁, ?_⟩⟩
    · rw [t₁]; exact hind.2.1.2
    · rw [t₁]; exact hu
    · rw [t₁]
      rintro (h | h)
      · exact f₂ h
      · exact hind.1.symm (Set.mem_singleton_iff.mp h)
    · rw [t₁]
    · rw [t₂]; exact hind.2.2.1.2
    · rw [t₂, union_pair_comm]; exact hu
    · rw [t₂]
      rintro (h | h)
      · exact f₁ h
      · exact hind.1 (Set.mem_singleton_iff.mp h)
    · rw [t₂]; exact union_pair_comm s.val e₁ e₂
end ConfFamily
