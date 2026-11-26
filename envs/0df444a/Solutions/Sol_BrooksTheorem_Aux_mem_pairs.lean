-- Prove2me | solution 1 for BrooksTheorem.Aux.mem_pairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:32:49.115959+00:00
-- url     : https://prove2.me/submissions/bbd74b15-3b99-415b-8482-a40037bc7b1d

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_BrooksCore
public import Theorems.Thm_BrooksTheorem_Aux_restr_adj
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
theorem _root_.solution {H : SimpleGraph V} {p : V × V} : p ∈ pairs H ↔ H.Adj p.1 p.2 := by
  simp [pairs]
end BrooksTheorem.Aux
