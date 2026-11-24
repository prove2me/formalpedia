-- Prove2me | solution 1 for BondySimonovits.mem_layer_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:10:45.390571+00:00
-- url     : https://prove2.me/submissions/6460b1ec-d65f-4841-a17c-0e2a0feb55e0

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
theorem _root_.solution (x : V) : x ∈ layer K x 0 := by
  rw [mem_layer]; exact ⟨Reachable.refl x, SimpleGraph.dist_self⟩
end BondySimonovits
