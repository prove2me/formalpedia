-- Prove2me | solution 1 for BrooksTheorem.Aux.nb_eq_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:37:32.841632+00:00
-- url     : https://prove2.me/submissions/e338a867-2a7f-48f1-8fdc-aca6db6efea0

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_BrooksCore
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
theorem _root_.solution [DecidableEq V] {H : SimpleGraph V} {k : ℕ} (hdeg : ∀ v, (nb H v).card ≤ k)
    {w p : V}
    {Q : Finset V} (hQ : Q ⊆ nb H w) (hp : H.Adj w p) (hpQ : p ∉ Q) (hcard : k ≤ Q.card + 1) :
    nb H w = insert p Q := by
  symm
  apply eq_of_subset_of_card_le
  · intro u hu
    rw [mem_insert] at hu
    rcases hu with rfl | hu
    · exact mem_nb.2 hp
    · exact hQ hu
  · rw [card_insert_of_notMem hpQ]; exact (hdeg w).trans hcard
end BrooksTheorem.Aux
