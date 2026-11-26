-- Prove2me | solution 1 for BrooksTheorem.Aux.nb_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:30:14.019145+00:00
-- url     : https://prove2.me/submissions/4483312b-afd9-40aa-a6b2-dda28eec8c82

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_Cycle
public import Theorems.Thm_BrooksTheorem_Aux_sq_adj
public import Theorems.Thm_BrooksTheorem_Aux_sq_ne
public import Theorems.Thm_BrooksTheorem_Aux_mem_nb
attribute [local simp] BrooksTheorem.Aux.mem_nb



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) (h2 : ∀ v, (nb G v).card = 2) (v0 v1 : V) (h01 : G.Adj v0 v1)
include h2 h01
namespace BrooksTheorem.Aux
theorem _root_.solution [DecidableEq V] (n : ℕ) :
    nb G (sq G v0 v1 (n + 1)) = {sq G v0 v1 n, sq G v0 v1 (n + 2)} := by
  symm
  apply eq_of_subset_of_card_le
  · intro u hu
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact mem_nb.2 (sq_adj G h2 v0 v1 h01 n).symm
    · exact mem_nb.2 (sq_adj G h2 v0 v1 h01 (n + 1))
  · rw [h2, card_pair (sq_ne G h2 v0 v1 n).symm]
end BrooksTheorem.Aux
