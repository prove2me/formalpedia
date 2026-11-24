-- Prove2me | solution 1 for BondySimonovits.ecount_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:06:46.196286+00:00
-- url     : https://prove2.me/submissions/0f20dbe9-f24e-44b7-b049-4ac221cbabb9

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
theorem _root_.solution (A B : Finset V) (h : ∀ a ∈ A, ∀ b ∈ B, ¬ K.Adj a b) :
    ecount K A B = 0 := by
  unfold ecount
  refine Finset.sum_eq_zero (fun a ha => ?_)
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun b hb => h a ha b hb
end BondySimonovits
