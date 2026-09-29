-- Prove2me | solution 1 for CubicP3Partition.kelmans_admissible_has_p3path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T21:44:44.590016+00:00
-- url     : https://prove2.me/submissions/bc0ffbe0-4252-4cdc-a3b4-db6a32ed926b

import Definitions.Def_cubic_p3_partition_models

open CubicP3Partition

theorem solution : ∀ (W : Type) [Fintype W], ∀ G : SimpleGraph W,
    Cubic G → ThreeVertexConnected G → Fintype.card W % 6 = 0 →
    Nonempty (P3Path G) := by
  intro W hW G hCub hCon hCard
  have h4 : 4 ≤ Fintype.card W := hCon.1
  have hWne : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v⟩ := hWne
  have h3 : Nat.card {w : W // G.Adj v w} = 3 := hCub v
  have hne : Nat.card {w : W // G.Adj v w} ≠ 0 := by omega
  have _fin : Finite {w : W // G.Adj v w} := Nat.finite_of_card_ne_zero hne
  have _ft : Fintype {w : W // G.Adj v w} := Fintype.ofFinite _
  have hcard : Fintype.card {w : W // G.Adj v w} = 3 := by
    rw [Fintype.card_eq_nat_card]
    exact h3
  obtain ⟨a, b, hab⟩ :=
    Fintype.exists_pair_of_one_lt_card (α := {w : W // G.Adj v w}) (by omega)
  refine ⟨⟨a.val, v, b.val, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (G.ne_of_adj a.property).symm
  · exact G.ne_of_adj b.property
  · exact fun h => hab (Subtype.ext h)
  · exact G.adj_symm a.property
  · exact b.property
