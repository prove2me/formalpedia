-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.not_isSynchronizing_of_ne_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:47:15.281136+00:00
-- url     : https://prove2.me/submissions/48d5b1bb-066a-4aff-9b5b-b39d74c486a7

module
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Theorems.Thm_BalanceSpecification_FiveSymbol_markerLeft_append_shortlex_mem
public import Theorems.Thm_BalanceSpecification_FiveSymbol_shortlex_append_markerRight_mem
public import Theorems.Thm_BalanceSpecification_length_shortlexWord_le
public import Theorems.Thm_BalanceSpecification_not_mem_language_of_forbidden
public import Theorems.Thm_BalanceSpecification_shortlexWord_surjective


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol
namespace BalanceSpecification.FiveSymbol
theorem _root_.solution {w : Word Alphabet}
    (hw : w ∈ language shift) (hwne : w ≠ []) : ¬ IsSynchronizing (language shift) w := by
  obtain ⟨j, rfl⟩ := shortlexWord_surjective w
  have hj : 1 ≤ j := by
    have hlength := length_shortlexWord_le (A := Alphabet) j
    have hpos : 0 < (shortlexWord (A := Alphabet) j).length :=
      List.length_pos_iff.mpr hwne
    omega
  intro hsync
  have hleft := markerLeft_append_shortlex_mem hj hw
  have hright := shortlex_append_markerRight_mem hj hw
  have hforbidden : forbiddenWord j ∈ language shift := hsync.2 (markerLeft j) (markerRight j) hleft hright
  exact (not_mem_language_of_forbidden (F := forbiddenWords) ⟨j, hj, rfl⟩) hforbidden
end BalanceSpecification.FiveSymbol
