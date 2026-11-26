-- Prove2me | solution 1 for BrooksTheorem.Aux.restr_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:31:44.352705+00:00
-- url     : https://prove2.me/submissions/d20b4548-584f-4e98-b973-1a9c38999fce

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_BrooksCore

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*}
namespace BrooksTheorem.Aux
theorem _root_.solution {H : SimpleGraph V} {S : Set V} {u v : V} :
    (restr H S).Adj u v ↔ H.Adj u v ∧ u ∈ S ∧ v ∈ S := Iff.rfl
end BrooksTheorem.Aux
