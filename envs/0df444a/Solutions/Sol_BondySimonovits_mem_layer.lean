-- Prove2me | solution 1 for BondySimonovits.mem_layer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:05:27.300306+00:00
-- url     : https://prove2.me/submissions/695ea2a4-a5a5-4711-9d52-3c1612efebdb

module
public import Definitions.Def_BondySimonovitsLib_BSCycle
public import Definitions.Def_BondySimonovitsLib_BSGrowth

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} [Fintype V] [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj]
namespace BondySimonovits
theorem _root_.solution {x v : V} {i : ℕ} : v ∈ layer K x i ↔ K.Reachable x v ∧ K.dist x v = i := by
  simp [layer]
end BondySimonovits
