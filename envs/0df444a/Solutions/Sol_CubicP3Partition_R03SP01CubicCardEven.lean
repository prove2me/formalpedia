-- Prove2me | solution 1 for CubicP3Partition.R03SP01CubicCardEven
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T09:58:32.460636+00:00
-- url     : https://prove2.me/submissions/38ef6ebc-fe02-4aa7-92e0-5cb56fa1c0bb

import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_e44e91d0f9_r03_sp01_divisibility_candidate_v1

namespace CubicP3Partition

set_option maxHeartbeats 1000000

lemma r03_degree_eq_simpleGraph_degree {V : Type} [Fintype V]
    (G : SimpleGraph V) (v : V) [DecidableRel G.Adj] :
    CubicP3Partition.degree G v = G.degree v := by
  classical
  rw [CubicP3Partition.degree]
  rw [← G.card_neighborSet_eq_degree v]
  exact Nat.card_eq_fintype_card


end CubicP3Partition

open CubicP3Partition
theorem solution {V : Type} [Fintype V]
    (G : SimpleGraph V) (hG : CubicP3Partition.Cubic G) :
    Even (Fintype.card V) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  have hsum : ∑ v, G.degree v = 3 * Fintype.card V := by
    calc
      ∑ v, G.degree v = ∑ v, 3 := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [← r03_degree_eq_simpleGraph_degree G v]
        exact hG v
      _ = 3 * Fintype.card V := by simp [mul_comm]
  have hhand : ∑ v, G.degree v = 2 * G.edgeFinset.card :=
    G.sum_degrees_eq_twice_card_edges
  have hmul : 3 * Fintype.card V = 2 * G.edgeFinset.card := by
    exact hsum.symm.trans hhand
  apply Nat.even_iff.mpr
  omega
