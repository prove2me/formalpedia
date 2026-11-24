-- Prove2me | solution 1 for BondySimonovits.layer_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:07:19.863338+00:00
-- url     : https://prove2.me/submissions/badf5885-11a5-4d2b-976a-133cbb30e49b

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
theorem _root_.solution (x : V) {i j : ℕ} (h : i ≠ j) : Disjoint (layer K x i) (layer K x j) := by
  rw [Finset.disjoint_left]
  intro v hi hj
  rw [mem_layer] at hi hj
  exact h (hi.2.symm.trans hj.2)
end BondySimonovits
