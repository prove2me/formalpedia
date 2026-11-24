-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.exists_map_some_of_markerFree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:22:43.805572+00:00
-- url     : https://prove2.me/submissions/0bff079e-94ef-41d1-a0fa-3e0368866db1

module
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerExtension

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*}
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution {w : Word (Option A)} (hw : none ∉ w) :
    ∃ v : Word A, w = v.map some := by
  induction w with
  | nil => exact ⟨[], rfl⟩
  | cons a w ih =>
    cases a with
    | none => exact False.elim (hw List.mem_cons_self)
    | some a =>
      obtain ⟨v, rfl⟩ := ih (fun h => hw (List.mem_cons_of_mem _ h))
      exact ⟨a :: v, rfl⟩
end BalanceSpecification.MarkerExtension
