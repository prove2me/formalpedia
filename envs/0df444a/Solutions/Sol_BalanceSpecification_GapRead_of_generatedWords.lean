-- Prove2me | solution 1 for BalanceSpecification.GapRead.of_generatedWords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:33:02.573713+00:00
-- url     : https://prove2.me/submissions/19814cb6-015b-44aa-84d6-b79ea1f3f211

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGap
public import Theorems.Thm_BalanceSpecification_GapRead_append
public import Theorems.Thm_BalanceSpecification_GapRead_generator

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
open BalanceSpecification.GapRead
variable {S : Set ℕ} {a b c : ℕ} {u v : Word Bool}
namespace BalanceSpecification.GapRead
theorem _root_.solution {w : Word Bool} (hw : w ∈ generatedWords (sGapCode S)) :
    GapRead S 0 w 0 := by
  obtain ⟨ws, hws, rfl⟩ := hw
  induction ws with
  | nil => exact .nil 0
  | cons w ws ih =>
    obtain ⟨s, hs, rfl⟩ := hws w List.mem_cons_self
    exact (generator hs).append (ih (fun v hv => hws v (List.mem_cons_of_mem _ hv)))
end BalanceSpecification.GapRead
