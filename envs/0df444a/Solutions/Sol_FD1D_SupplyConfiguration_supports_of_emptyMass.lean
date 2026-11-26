-- Prove2me | solution 1 for FD1D.SupplyConfiguration.supports_of_emptyMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:38:15.169154+00:00
-- url     : https://prove2.me/submissions/5f571edf-d5dc-481d-a329-cb4574150fb1

import Definitions.Def_FD1D_Transport
import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Spatial

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory
open FD1D.SupplyConfiguration
variable {L m : ℕ}
namespace FD1D.SupplyConfiguration
theorem _root_.solution (C : SupplyConfiguration L m)
    (q : DyadicMass L)
    (hempty : ∀ i, C.leafCount i = 0 → q.leafMass i = 0) :
    C.Supports q := by
  intro i hmass
  have hcount : 0 < C.leafCount i := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hmass.ne' (hempty i hzero)
  rcases Finset.card_pos.mp hcount with ⟨j, hj⟩
  exact ⟨j, (Finset.mem_filter.mp hj).2⟩
end FD1D.SupplyConfiguration
