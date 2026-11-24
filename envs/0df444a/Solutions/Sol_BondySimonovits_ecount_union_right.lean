-- Prove2me | solution 1 for BondySimonovits.ecount_union_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:06:14.832791+00:00
-- url     : https://prove2.me/submissions/9a79f219-afbc-4147-86b1-4a7955e18b33

module
public import Definitions.Def_BondySimonovitsLib_BSCycle
public import Definitions.Def_BondySimonovitsLib_BSGrowth

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj]
namespace BondySimonovits
theorem _root_.solution (A B B' : Finset V) (h : Disjoint B B') :
    ecount K A (B ∪ B') = ecount K A B + ecount K A B' := by
  unfold ecount
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)]
end BondySimonovits
