-- Prove2me | solution 1 for BondySimonovits.adj_levels
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:08:49.796072+00:00
-- url     : https://prove2.me/submissions/62122d0c-324f-4b71-acd4-0f427422019e

module
public import Definitions.Def_BondySimonovitsLib_BSBasic
public import Definitions.Def_BondySimonovitsLib_BSLayers
public import Theorems.Thm_BondySimonovits_dist_le_of_adj
public import Theorems.Thm_BondySimonovits_dist_ne_of_adj

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} (K : SimpleGraph V)
namespace BondySimonovits
theorem _root_.solution (f : V → Bool) (hf : ∀ u v, K.Adj u v → f u ≠ f v) {x u v : V}
    (hr : K.Reachable x u) (h : K.Adj u v) :
    K.Reachable x v ∧ (K.dist x v = K.dist x u + 1 ∨ K.dist x u = K.dist x v + 1) := by
  have hv := hr.trans h.reachable
  have a1 := dist_le_of_adj K hr h
  have a2 := dist_le_of_adj K hv h.symm
  have a3 := dist_ne_of_adj K f hf hr h
  exact ⟨hv, by omega⟩
end BondySimonovits
