-- Prove2me | solution 1 for BrooksTheorem.Aux.exists_not_mem_of_card_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:27:01.437916+00:00
-- url     : https://prove2.me/submissions/65696356-7398-49f6-9787-36154d93d0f9

module
public import Mathlib
public import Definitions.Def_BrooksLib_Greedy
public import Theorems.Thm_BrooksTheorem_Aux_mem_nb
attribute [local simp] BrooksTheorem.Aux.mem_nb

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*}
variable [Fintype V]
namespace BrooksTheorem.Aux
theorem _root_.solution {k : ℕ} (C : Finset (Fin k)) (h : C.card < k) :
    ∃ c : Fin k, c ∉ C := by
  by_contra hcon
  push Not at hcon
  have : (univ : Finset (Fin k)) ⊆ C := fun x _ => hcon x
  have := Finset.card_le_card this
  simp at this
  omega
end BrooksTheorem.Aux
