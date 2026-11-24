-- Prove2me | solution 1 for BondySimonovits.ecount_union_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:09:38.464536+00:00
-- url     : https://prove2.me/submissions/aa9bad67-72ad-412f-986a-ca1e55fdaa57

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
theorem _root_.solution (A A' B : Finset V) (h : Disjoint A A') :
    ecount K (A ∪ A') B = ecount K A B + ecount K A' B := by
  unfold ecount
  rw [Finset.sum_union h]
end BondySimonovits
