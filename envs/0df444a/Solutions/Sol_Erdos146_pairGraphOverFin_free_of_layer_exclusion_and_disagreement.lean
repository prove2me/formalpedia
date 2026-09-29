-- Prove2me | solution 1 for Erdos146.pairGraphOverFin_free_of_layer_exclusion_and_disagreement
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:42:37.336002+00:00
-- url     : https://prove2.me/submissions/2c4e0ad3-add5-47e3-845d-c05e32130630

import Definitions.Def_erdos146_core2
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Real.Basic
import Theorems.Thm_Erdos146_pairGraph_free_of_layer_exclusion_and_disagreement

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (hdepth : 1 < (depth : ℝ) * (certifiedWindowWidth / 2))
    (retained : Set (Bool × HammingWord dimension))
    (hexclusion :
      ∀ (side : Bool) (layer : Fin depth),
        retained ∉
          badPairLayerRetentionEvent
            (Fintype.card (PairLayer baseSize layer.val))
            dimension side (midpointBeta - entropySlack))
    (herror :
      ∀ layer : Fin depth,
        empiricalEntropyError
          (Fintype.card (PairLayer baseSize layer.val)) < entropySlack)
    (hdisagreement :
      ∀ (copy : SimpleGraph.Copy
          (pairParentSystem baseSize depth).graph
          (retainedHammingHost dimension radius retained))
        (layer : Fin depth),
          pairChildArrayAverageDisagreement
            (hbase.trans
              (pairLayer_card_ge_base baseSize layer.val hbase))
            (pairGraphCopyParentWords retained copy layer)
            (pairGraphCopyChildWords retained copy layer) ≤ tau) :
    (pairGraphOverFin baseSize depth).Free
      (retainedHammingHost dimension radius retained) := by
  exact (SimpleGraph.free_congr_left
    (pairGraphOverFinIso baseSize depth)).mp
      (pairGraph_free_of_layer_exclusion_and_disagreement
        hbase hdimension hdepth retained hexclusion herror hdisagreement)
