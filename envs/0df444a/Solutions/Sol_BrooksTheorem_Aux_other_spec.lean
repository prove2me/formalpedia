-- Prove2me | solution 1 for BrooksTheorem.Aux.other_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:27:48.098704+00:00
-- url     : https://prove2.me/submissions/2aac845e-3fd5-48d8-b28e-2e9776b04787

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_Cycle
public import Theorems.Thm_BrooksTheorem_Aux_mem_nb
attribute [local simp] BrooksTheorem.Aux.mem_nb



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*} [Fintype V]
namespace BrooksTheorem.Aux
theorem _root_.solution (G : SimpleGraph V) (h2 : ∀ v, (nb G v).card = 2) (a b : V) :
    G.Adj a (other G a b) ∧ other G a b ≠ b := by
  classical
  have hne : ((nb G a).erase b).Nonempty := by
    rw [← card_pos]
    have := pred_card_le_card_erase (s := nb G a) (a := b)
    have := h2 a
    omega
  have hmem := hne.choose_spec
  simp only [other, hne, ↓reduceDIte]
  rw [mem_erase, mem_nb] at hmem
  exact ⟨hmem.2, hmem.1⟩
end BrooksTheorem.Aux
