-- Prove2me | solution 1 for Erdos146.pairGraphOverFin_forall_exists_adj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:49:40.9563+00:00
-- url     : https://prove2.me/submissions/813c52ee-a183-41d7-a39b-aae7b20c0e95

import Definitions.Def_erdos146_core2
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_Erdos146_pairGraphOverFin_connected

namespace Erdos146

section
open Filter Finset SimpleGraph
open scoped Topology

theorem baseSize_le_pairVertex_card
    (baseSize depth : ℕ) :
    baseSize ≤ Fintype.card (PairVertex baseSize depth) := by
  calc
    baseSize = Fintype.card (PairLayer baseSize 0) :=
      (pairLayer_card_zero baseSize).symm
    _ ≤ Fintype.card (PairVertex baseSize depth) :=
      Fintype.card_le_of_embedding
        (pairLayerEmbedding baseSize depth 0 (by omega))

end

end Erdos146

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    (baseSize depth : ℕ)
    (hbase : 4 ≤ baseSize)
    (hdepth : 0 < depth) :
    ∀ vertex : Fin (Fintype.card (PairVertex baseSize depth)),
      ∃ neighbor,
        (pairGraphOverFin baseSize depth).Adj vertex neighbor := by
  have hcard : 2 ≤ Fintype.card (PairVertex baseSize depth) := by
    have hcard_base := baseSize_le_pairVertex_card baseSize depth
    omega
  letI : Nontrivial (Fin (Fintype.card (PairVertex baseSize depth))) :=
    Fin.nontrivial_iff_two_le.mpr hcard
  intro vertex
  exact
    (pairGraphOverFin_connected baseSize depth (by omega) hdepth).preconnected
      |>.exists_adj_of_nontrivial vertex
