-- Prove2me | solution 1 for C6BipartiteDomination.paper11K3_edge_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:56:30.354417+00:00
-- url     : https://prove2.me/submissions/00267195-797d-435b-b2d5-69b57fe1c437

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {w u : V} :
    (w, u) ∈ paper11K3Edges G D hCan hmax ↔
      w ∈ paper11K3Supports G D ∧
        u ∈ paperChosenRepairSet G D hCan hmax w := by
  classical
  simp [paper11K3Edges]
end C6BipartiteDomination
