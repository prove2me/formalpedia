-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.split_last_marker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:22:54.494949+00:00
-- url     : https://prove2.me/submissions/44a3cbbb-59be-485c-b19e-0c2cd3f1ce02

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
theorem _root_.solution (w : Word (Option A)) :
    (∃ v : Word A, w = v.map some) ∨
      ∃ u : Word (Option A), ∃ v : Word A, w = u ++ none :: v.map some := by
  induction w with
  | nil => exact Or.inl ⟨[], rfl⟩
  | cons o w ih =>
    rcases ih with ⟨v, rfl⟩ | ⟨u, v, rfl⟩
    · cases o with
      | none => exact Or.inr ⟨[], v, rfl⟩
      | some a => exact Or.inl ⟨a :: v, rfl⟩
    · exact Or.inr ⟨o :: u, v, rfl⟩
end BalanceSpecification.MarkerExtension
