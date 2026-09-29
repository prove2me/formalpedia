-- Prove2me | solution 1 for Erdos146.pairGraphOverFin_connected
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:14:17.499671+00:00
-- url     : https://prove2.me/submissions/3bdd0f6c-ec46-4b0f-87b1-4cc6ca966278

import Definitions.Def_erdos146_core2
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_Erdos146_ParentSystem_graph_adj_iff

namespace Erdos146

section
open Filter Finset SimpleGraph
open scoped Topology

theorem pairLayer_reaches_base (baseSize depth : ℕ) :
    ∀ (i : ℕ) (hi : i < depth + 1) (v : PairLayer baseSize i),
      ∃ a : Fin baseSize,
        (pairParentSystem baseSize depth).graph.Reachable
          (pairLayerEmbedding baseSize depth i hi v)
          (pairBaseVertex baseSize depth a) := by
  intro i
  induction i with
  | zero =>
      intro hi v
      exact ⟨v, SimpleGraph.Reachable.rfl⟩
  | succ i ih =>
      intro hi v
      change {parents : Finset (PairLayer baseSize i) // parents.card = 2} at v
      have hnonempty : v.val.Nonempty := by
        apply Finset.card_pos.mp
        omega
      obtain ⟨parent, hparent⟩ := hnonempty
      let lower := pairLayerEmbedding baseSize depth i (by omega) parent
      let upper := pairLayerEmbedding baseSize depth (i + 1) hi v
      have hedge :
          (pairParentSystem baseSize depth).graph.Adj upper lower := by
        apply (ParentSystem.graph_adj_iff _ upper lower).mpr
        constructor
        · intro heq
          have hlevels := congrArg
            (fun x : PairVertex baseSize depth => x.1.val) heq
          change i + 1 = i at hlevels
          omega
        · left
          change lower ∈ pairParents baseSize depth upper
          change lower ∈
            v.val.map (pairLayerEmbedding baseSize depth i (by omega))
          exact Finset.mem_map.mpr ⟨parent, hparent, rfl⟩
      obtain ⟨a, ha⟩ := ih (by omega) parent
      refine ⟨a, hedge.reachable.trans ?_⟩
      exact ha

theorem pairBaseVertices_reachable (baseSize depth : ℕ)
    (hdepth : 0 < depth) (a b : Fin baseSize) :
    (pairParentSystem baseSize depth).graph.Reachable
      (pairBaseVertex baseSize depth a)
      (pairBaseVertex baseSize depth b) := by
  classical
  letI pairDecidableEq : DecidableEq (PairLayer baseSize 0) := Classical.decEq _
  by_cases hab : a = b
  · subst b
    exact SimpleGraph.Reachable.rfl
  · let pair : PairLayer baseSize 1 :=
      ⟨{a, b}, Finset.card_pair hab⟩
    let bridge := pairLayerEmbedding baseSize depth 1 (by omega) pair
    have hadj (x : Fin baseSize) (hx : x = a ∨ x = b) :
        (pairParentSystem baseSize depth).graph.Adj
          bridge (pairBaseVertex baseSize depth x) := by
      apply (ParentSystem.graph_adj_iff _ bridge _).mpr
      constructor
      · intro heq
        have hlevels := congrArg
          (fun z : PairVertex baseSize depth => z.1.val) heq
        change 1 = 0 at hlevels
        omega
      · left
        change pairBaseVertex baseSize depth x ∈
          pairParents baseSize depth bridge
        have hxmem : x ∈ ({a, b} : Finset (PairLayer baseSize 0)) := by
          rcases hx with hxa | hxb
          · rw [hxa]
            exact @Finset.mem_insert_self (PairLayer baseSize 0)
              pairDecidableEq a ({b} : Finset (PairLayer baseSize 0))
          · rw [hxb]
            exact @Finset.mem_insert_of_mem (PairLayer baseSize 0)
              pairDecidableEq ({b} : Finset (PairLayer baseSize 0)) b a
              (Finset.mem_singleton_self b)
        change
          pairLayerEmbedding baseSize depth 0 (by omega) x ∈
            ({a, b} : Finset (PairLayer baseSize 0)).map
              (pairLayerEmbedding baseSize depth 0 (by omega))
        exact Finset.mem_map.mpr ⟨x, hxmem, rfl⟩
    exact (hadj a (Or.inl rfl)).symm.reachable.trans
      (hadj b (Or.inr rfl)).reachable

theorem pairGraph_connected (baseSize depth : ℕ)
    (hbase : 0 < baseSize) (hdepth : 0 < depth) :
    (pairParentSystem baseSize depth).graph.Connected := by
  let root : Fin baseSize := ⟨0, hbase⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨pairBaseVertex baseSize depth root, ?_⟩
  rintro ⟨⟨i, hi⟩, v⟩
  obtain ⟨a, ha⟩ := pairLayer_reaches_base baseSize depth i hi v
  exact (pairBaseVertices_reachable baseSize depth hdepth root a).trans ha.symm

end

end Erdos146

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution (baseSize depth : ℕ)
    (hbase : 0 < baseSize) (hdepth : 0 < depth) :
    (pairGraphOverFin baseSize depth).Connected :=
  (pairGraphOverFinIso baseSize depth).connected_iff.mp
    (pairGraph_connected baseSize depth hbase hdepth)
