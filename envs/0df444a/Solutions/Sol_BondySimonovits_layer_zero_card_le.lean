-- Prove2me | solution 1 for BondySimonovits.layer_zero_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:10:39.921144+00:00
-- url     : https://prove2.me/submissions/372cec3f-f3b6-4999-bfb9-9131786be9c3

module
public import Definitions.Def_BondySimonovitsLib_BSCycle
public import Definitions.Def_BondySimonovitsLib_BSGrowth
public import Theorems.Thm_BondySimonovits_mem_layer

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} [Fintype V] [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj]
namespace BondySimonovits
theorem _root_.solution (x : V) : (layer K x 0).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [mem_layer] at ha hb
  exact ((ha.1.dist_eq_zero_iff).1 ha.2).symm.trans ((hb.1.dist_eq_zero_iff).1 hb.2)
end BondySimonovits
