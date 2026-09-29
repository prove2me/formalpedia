-- Prove2me | solution 1 for CubicP3Partition.exists_induced_residual_isolated_vertex
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:46:26.476001+00:00
-- url     : https://prove2.me/submissions/7eda0523-9137-4cab-999c-10d6fb784ef9

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
    ∃ v : R, degree (G.induce (R : Set V)) v = 0 := by
  classical
  let H : SimpleGraph R := G.induce (R : Set V)
  have hcanon : ∀ v : R, degree H v = H.degree v := by
    intro v
    rw [CubicP3Partition.degree]
    rw [← H.card_neighborSet_eq_degree v]
    exact Nat.card_eq_fintype_card
  by_contra h
  push Not at h
  have hone : ∀ v : R, H.degree v = 1 := by
    intro v
    have hne : degree H v ≠ 0 := h v
    have hle : H.degree v ≤ 1 := by
      rw [← hcanon v]
      exact hdeg v
    rw [hcanon v] at hne
    omega
  have hsum : ∑ v : R, H.degree v = 3 := by
    calc
      (∑ v : R, H.degree v) = ∑ v : R, 1 := by
        apply Finset.sum_congr rfl
        intro v hv
        exact hone v
      _ = 3 := by simpa using hRcard
  rw [H.sum_degrees_eq_twice_card_edges] at hsum
  omega

