-- Prove2me | solution 1 for DiracCycle.exists_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:53:05.202168+00:00
-- url     : https://prove2.me/submissions/ca52b2a2-b779-4e5a-a2c4-ace48725f5ae

module
public import Mathlib
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
public import Definitions.Def_DiracCycleLib_DiracCycle
public import Theorems.Thm_Menger_Aux_Sep_symm


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open DiracCycle
open Hamiltonicity
variable {V : Type*} {G : SimpleGraph V}
namespace DiracCycle
theorem _root_.solution : ∀ (n : ℕ) (R U : Finset ℕ), #U = n → #U + 2 ≤ #R →
    ∃ a ∈ R, ∃ b ∈ R, a < b ∧ ∀ u ∈ U, ¬ (a < u ∧ u < b) := by
  intro n
  induction n with
  | zero =>
    intro R U hU hR
    rw [Finset.card_eq_zero] at hU
    subst hU
    obtain ⟨a, ha, b, hb, hab⟩ := (Finset.one_lt_card (s := R)).1 (by simp at hR; omega)
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨a, ha, b, hb, h, by simp⟩
    · exact ⟨b, hb, a, ha, h, by simp⟩
  | succ n ih =>
    intro R U hU hR
    have hRne : R.Nonempty := Finset.card_pos.1 (by omega)
    set a := R.min' hRne with ha
    have hR'ne : (R.erase a).Nonempty :=
      Finset.card_pos.1 (by rw [Finset.card_erase_of_mem (R.min'_mem hRne)]; omega)
    set b := (R.erase a).min' hR'ne with hb
    have hbmem := (R.erase a).min'_mem hR'ne
    have hab : a < b := by
      rw [Finset.mem_erase] at hbmem
      exact lt_of_le_of_ne (R.min'_le _ hbmem.2) (Ne.symm hbmem.1)
    by_cases hgap : ∀ u ∈ U, ¬ (a < u ∧ u < b)
    · exact ⟨a, R.min'_mem hRne, b, Finset.mem_of_mem_erase hbmem, hab, hgap⟩
    push Not at hgap
    obtain ⟨u, hu, hau, hub⟩ := hgap
    obtain ⟨a', ha', b', hb', hab', hgap'⟩ := ih (R.erase a) (U.erase u)
      (by rw [Finset.card_erase_of_mem hu]; omega)
      (by rw [Finset.card_erase_of_mem hu, Finset.card_erase_of_mem (R.min'_mem hRne)]; omega)
    refine ⟨a', Finset.mem_of_mem_erase ha', b', Finset.mem_of_mem_erase hb', hab', ?_⟩
    intro w hw
    by_cases hwu : w = u
    · subst hwu
      have : b ≤ a' := (R.erase a).min'_le _ ha'
      omega
    · exact hgap' w (Finset.mem_erase.2 ⟨hwu, hw⟩)
end DiracCycle
