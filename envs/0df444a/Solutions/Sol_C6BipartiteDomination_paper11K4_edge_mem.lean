-- Prove2me | solution 1 for C6BipartiteDomination.paper11K4_edge_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:59:26.602845+00:00
-- url     : https://prove2.me/submissions/20d21670-724e-4d13-9cf8-ff19971d91bd

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {w u : V} :
    (w, u) ∈ paper11K4Edges G D hCan hmax ↔
      w ∈ paper11K4Supports G D ∧
        u ∈ paperChosenRepairSet G D hCan hmax w := by
  classical
  simp [paper11K4Edges]
end C6BipartiteDomination
