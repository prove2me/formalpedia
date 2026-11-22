-- Prove2me | solution 1 for ConfFamily.toRLTSI_LPV
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:05:33.119537+00:00
-- url     : https://prove2.me/submissions/8b51f4a6-1903-4d5a-acb5-8d56e0a8693f

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Family_LTSI
import Definitions.Def_EventStructures_Stable_LTSI
import Theorems.Thm_ConfFamily_esRStep_bwd
import Theorems.Thm_ConfFamily_config_diff_pair
import Theorems.Thm_ConfFamily_inter_diff_union
import Theorems.Thm_P2M_ConfFamily_inter_diff_union__310b7debc330
import Theorems.Thm_Bisimilar_symm
import Theorems.Thm_ConfFamily_Indep_symm
import Theorems.Thm_ConfFamily_toLTSI_LPV


set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
open ConfFamily
variable {F}
namespace ConfFamily
theorem _root_.solution (hF : Stable F) : RLTSI.LPV (toRLTSI F) where
  toLPV := by
    refine { indep_step_left := ?_, indep_step_right := ?_, indep_irrefl := ?_,
             indep_symm := ?_, square := ?_ }
    · rintro s (a | a) s₁ (b | b) s₂ h <;> try exact h.elim
      · exact (toLTSI_LPV F).indep_step_left h
      · obtain ⟨e₁, -, -, hin₁, -, hl₁, -, hc₁, -, ht₁, -⟩ := h
        exact esRStep_bwd (by rw [ht₁]; exact hc₁) hin₁ hl₁ ht₁
    · rintro s (a | a) s₁ (b | b) s₂ h <;> try exact h.elim
      · exact (toLTSI_LPV F).indep_step_right h
      · obtain ⟨-, e₂, -, -, hin₂, -, hl₂, -, hc₂, -, ht₂⟩ := h
        exact esRStep_bwd (by rw [ht₂]; exact hc₂) hin₂ hl₂ ht₂
    · rintro s (a | a) s' h
      · exact (toLTSI_LPV F).indep_irrefl h
      · obtain ⟨e₁, e₂, hne, hin₁, -, -, -, -, -, ht₁, ht₂⟩ := h
        refine hne ?_
        have : e₁ ∉ s'.val := by rw [ht₁]; exact fun hx => hx.2 rfl
        rw [ht₂] at this
        by_contra hne'
        exact this ⟨hin₁, fun h => hne' (Set.mem_singleton_iff.mp h)⟩
    · rintro s (a | a) s₁ (b | b) s₂ h <;> try exact h.elim
      · exact (toLTSI_LPV F).indep_symm h
      · obtain ⟨e₁, e₂, hne, hin₁, hin₂, hl₁, hl₂, hc₁, hc₂, ht₁, ht₂⟩ := h
        exact ⟨e₂, e₁, hne.symm, hin₂, hin₁, hl₂, hl₁, hc₂, hc₁, ht₂, ht₁⟩
    · rintro s (a | a) s₁ (b | b) s₂ h <;> try exact h.elim
      · exact (toLTSI_LPV F).square h
      · obtain ⟨e₁, e₂, hne, hin₁, hin₂, hl₁, hl₂, hc₁, hc₂, ht₁, ht₂⟩ := h
        refine ⟨⟨(s.val \ {e₁}) ∩ (s.val \ {e₂}), config_diff_pair hF hc₁ hc₂ s.2⟩, ?_, ?_⟩
        · refine ⟨e₂, ⟨config_diff_pair hF hc₁ hc₂ s.2, ?_⟩, ?_, hl₂, ?_⟩
          · rw [inter_diff_union hin₂ hne]; exact hc₁
          · exact fun hx => hx.2.2 rfl
          · rw [ht₁, inter_diff_union hin₂ hne]
        · refine ⟨e₁, ⟨config_diff_pair hF hc₁ hc₂ s.2, ?_⟩, ?_, hl₁, ?_⟩
          · rw [inter_diff_union' hin₁ hne]; exact hc₂
          · exact fun hx => hx.1.2 rfl
          · rw [ht₂, inter_diff_union' hin₁ hne]
  BTI := by
    intro s a s₁ b s₂ h₁ h₂ hdist
    obtain ⟨e₁, hen₁, hfr₁, hl₁, ht₁⟩ := h₁
    obtain ⟨e₂, hen₂, hfr₂, hl₂, ht₂⟩ := h₂
    have hin₁ : e₁ ∈ s.val := ht₁ ▸ Set.mem_union_right _ rfl
    have hin₂ : e₂ ∈ s.val := ht₂ ▸ Set.mem_union_right _ rfl
    have hd₁ : s₁.val = s.val \ {e₁} := by
      rw [ht₁]; ext x
      constructor
      · exact fun hx => ⟨Or.inl hx, fun h => hfr₁ ((Set.mem_singleton_iff.mp h) ▸ hx)⟩
      · rintro ⟨hx | hx, hne⟩
        · exact hx
        · exact absurd (Set.mem_singleton_iff.mp hx) (fun h => hne (h ▸ rfl))
    have hd₂ : s₂.val = s.val \ {e₂} := by
      rw [ht₂]; ext x
      constructor
      · exact fun hx => ⟨Or.inl hx, fun h => hfr₂ ((Set.mem_singleton_iff.mp h) ▸ hx)⟩
      · rintro ⟨hx | hx, hne⟩
        · exact hx
        · exact absurd (Set.mem_singleton_iff.mp hx) (fun h => hne (h ▸ rfl))
    have hne : e₁ ≠ e₂ := by
      rintro rfl
      exact hdist.elim (fun hab => hab (hl₁.symm.trans hl₂))
        (fun hs => hs (Subtype.ext (hd₁.trans hd₂.symm)))
    exact ⟨e₁, e₂, hne, hin₁, hin₂, hl₁, hl₂, hd₁ ▸ s₁.2, hd₂ ▸ s₂.2, hd₁, hd₂⟩
end ConfFamily
