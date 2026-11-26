-- Prove2me | solution 1 for BrooksTheorem.Aux.addE_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:31:44.908305+00:00
-- url     : https://prove2.me/submissions/ffd79b69-ebc4-41b6-9e75-3fcd43d5822a

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
theorem _root_.solution {H : SimpleGraph V} {x z u v : V} :
    (H ⊔ edge x z).Adj u v ↔ H.Adj u v ∨ ((u = x ∧ v = z ∨ u = z ∧ v = x) ∧ u ≠ v) := by
  rw [sup_adj, edge_adj]
end BrooksTheorem.Aux
