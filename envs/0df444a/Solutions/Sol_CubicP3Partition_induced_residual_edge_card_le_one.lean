-- Prove2me | solution 1 for CubicP3Partition.induced_residual_edge_card_le_one
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:46:41.61278+00:00
-- url     : https://prove2.me/submissions/2cfc39ec-936a-4db5-820f-668bed37fd07

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

universe u

noncomputable section

variable {V : Type u}


end
end CubicP3Partition

open CubicP3Partition
universe u
variable {V : Type u}
theorem solution
    {G : SimpleGraph V} {R : Finset V}
    (hRcard : Fintype.card R = 3)
    (hdeg : ∀ v : R, degree (G.induce (R : Set V)) v ≤ 1) :
    Nat.card (G.induce (R : Set V)).edgeSet ≤ 1 := by
  classical
  let H : SimpleGraph R := G.induce (R : Set V)
  change Nat.card H.edgeSet ≤ 1
  have hcanon : ∀ v : R, degree H v = H.degree v := by
    intro v
    rw [CubicP3Partition.degree]
    rw [← H.card_neighborSet_eq_degree v]
    exact Nat.card_eq_fintype_card
  have hsum : ∑ v : R, H.degree v ≤ 3 := by
    calc
      (∑ v : R, H.degree v) =
          ∑ v : R, degree H v := by
        apply Finset.sum_congr rfl
        intro v hv
        exact (hcanon v).symm
      _ ≤ ∑ _v : R, 1 := by
        apply Finset.sum_le_sum
        intro v hv
        exact hdeg v
      _ = 3 := by simpa using hRcard
  rw [H.sum_degrees_eq_twice_card_edges] at hsum
  have hle : H.edgeFinset.card ≤ 1 := by
    by_contra hnot
    have hge : 2 ≤ H.edgeFinset.card := by omega
    have hmul : 2 * 2 ≤ 2 * H.edgeFinset.card :=
      Nat.mul_le_mul_left 2 hge
    norm_num at hmul
    have hbad : 4 ≤ 3 := hmul.trans hsum
    omega
  rw [Nat.card_eq_fintype_card, ← H.edgeFinset_card]
  exact hle

