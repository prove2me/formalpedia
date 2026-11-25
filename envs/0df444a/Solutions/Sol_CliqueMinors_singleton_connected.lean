-- Prove2me | solution 1 for CliqueMinors.singleton_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:40:49.937401+00:00
-- url     : https://prove2.me/submissions/0252fa0e-72e2-4f79-be60-c4f90a0e3499

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
public import Theorems.Thm_CliqueMinors_induce_connected_of_root

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
open Relation
namespace CliqueMinors
theorem _root_.solution (G : SimpleGraph V) (v : V) :
    (G.induce (({v} : Finset V) : Set V)).Connected :=
  induce_connected_of_root G _ v (Finset.mem_singleton_self _) fun w hw => by
    rw [Finset.mem_singleton.1 hw]
end CliqueMinors
