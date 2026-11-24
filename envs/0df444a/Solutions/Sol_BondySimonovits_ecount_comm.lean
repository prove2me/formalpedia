-- Prove2me | solution 1 for BondySimonovits.ecount_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:06:37.747801+00:00
-- url     : https://prove2.me/submissions/92c13fbc-ce0b-42bb-8ccf-2e29ec2620c4

module
public import Definitions.Def_BondySimonovitsLib_BSCycle
public import Definitions.Def_BondySimonovitsLib_BSGrowth

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj]
omit [DecidableEq V]
namespace BondySimonovits
theorem _root_.solution (A B : Finset V) : ecount K A B = ecount K B A := by
  unfold ecount
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => ?_))
  simp [K.adj_comm]
end BondySimonovits
