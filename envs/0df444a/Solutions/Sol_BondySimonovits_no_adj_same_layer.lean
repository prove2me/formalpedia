-- Prove2me | solution 1 for BondySimonovits.no_adj_same_layer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:07:37.137836+00:00
-- url     : https://prove2.me/submissions/e18e3232-24c0-4e43-92ac-4914e6119544

module
public import Definitions.Def_BondySimonovitsLib_BSCycle
public import Definitions.Def_BondySimonovitsLib_BSGrowth
public import Theorems.Thm_BondySimonovits_mem_layer
public import Theorems.Thm_BondySimonovits_dist_ne_of_adj


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} [Fintype V] [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj]
variable (f : V → Bool) (hf : ∀ u v, K.Adj u v → f u ≠ f v)
include hf
namespace BondySimonovits
theorem _root_.solution (x : V) (i : ℕ) :
    ∀ a ∈ layer K x i, ∀ b ∈ layer K x i, ¬ K.Adj a b := by
  intro a ha b hb h
  rw [mem_layer] at ha hb
  exact dist_ne_of_adj K f hf ha.1 h (ha.2.trans hb.2.symm)
end BondySimonovits
