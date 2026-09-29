-- Prove2me | solution 1 for CubicP3Partition.induced_residual_isolated_no_residual_neighbor
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:46:43.243199+00:00
-- url     : https://prove2.me/submissions/1f49b2b6-c9b3-44bd-840d-409b9f3a50fa

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

universe u

noncomputable section

variable {V : Type u}

/-- A three-vertex induced graph of maximum degree one has an isolated vertex. -/
theorem exists_induced_residual_isolated_vertex
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


end
end CubicP3Partition

open CubicP3Partition
universe u
variable {V : Type u}
theorem solution
    {G : SimpleGraph V} {R : Finset V}
    {v : R} (hv : degree (G.induce (R : Set V)) v = 0) :
    ∀ w : V, G.Adj v.1 w → w ∉ (R : Set V) := by
  classical
  intro w hwAdj hwR
  let H : SimpleGraph R := G.induce (R : Set V)
  have hsub : Nonempty {x : R // H.Adj v x} := by
    exact ⟨⟨⟨w, hwR⟩, SimpleGraph.induce_adj.mpr hwAdj⟩⟩
  have hpos : 0 < Nat.card {x : R // H.Adj v x} :=
    Nat.card_pos_iff.mpr ⟨hsub, inferInstance⟩
  have hvH : degree H v = 0 := by
    simpa [H] using hv
  rw [CubicP3Partition.degree] at hvH
  omega

