-- Prove2me | solution 1 for BKAR.Forest.mem_edgeSetOrderTails_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:45:25.779408+00:00
-- url     : https://prove2.me/submissions/ec7a8371-46ac-461e-aaa6-c30e32d5e1aa

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]
namespace BKAR.Forest
theorem _root_.solution
    (S : Finset (Edge V))
    {x : Σ _ : {y : Edge V // y ∈ S}, List (Edge V)} :
    x ∈ edgeSetOrderTails S ↔
      x.2 ∈ edgeSetOrders (S.erase x.1.val) := by
  rw [edgeSetOrderTails, Finset.mem_sigma]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨Finset.mem_attach S x.1, h⟩
end BKAR.Forest
