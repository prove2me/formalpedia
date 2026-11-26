-- Prove2me | solution 1 for BrooksTheorem.Aux.nb_addE_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:37:15.353278+00:00
-- url     : https://prove2.me/submissions/6f45a79a-d0ea-477a-9222-627951d44be3

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_BrooksCore
public import Theorems.Thm_BrooksTheorem_Aux_restr_adj
public import Theorems.Thm_BrooksTheorem_Aux_addE_adj
public import Theorems.Thm_BrooksTheorem_Aux_mem_nb
attribute [local simp] BrooksTheorem.Aux.mem_nb


attribute [local simp] BrooksTheorem.Aux.restr_adj

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*}
variable [Fintype V]
namespace BrooksTheorem.Aux
theorem _root_.solution [DecidableEq V] (H : SimpleGraph V) (S : Set V) {x z w w' pw : V}
    (hw : (w = x ∧ w' = z) ∨ (w = z ∧ w' = x)) (hpwS : pw ∉ S) :
    nb (restr H S ⊔ edge x z) w ⊆ insert w' ((nb H w).erase pw) := by
  intro u hu
  rw [mem_nb, addE_adj] at hu
  rw [mem_insert, mem_erase, mem_nb]
  rcases hu with ⟨hu1, _, hu3⟩ | ⟨hu, _⟩
  · exact Or.inr ⟨fun h => hpwS (h ▸ hu3), hu1⟩
  · left
    rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp_all
end BrooksTheorem.Aux
