-- Prove2me | solution 1 for BrooksTheorem.Aux.nb_restr_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:37:01.437223+00:00
-- url     : https://prove2.me/submissions/8c84bbd1-4e2c-42f8-bf50-16a21302cc9f

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
theorem _root_.solution (H : SimpleGraph V) (S : Set V) (v : V) : nb (restr H S) v ⊆ nb H v :=
  fun _ hu => (mem_nb.1 hu).1 |> mem_nb.2
end BrooksTheorem.Aux
