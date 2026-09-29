-- Prove2me | solution 1 for DreyfusWagner.Steiner.steinerTree_isAcyclic
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:32:58.628021+00:00
-- url     : https://prove2.me/submissions/9cdd2df9-72a9-424c-b3d1-d17304b1d30c

import Mathlib
import Definitions.Def_DreyfusWagner_Steiner_SteinerProblem

namespace DreyfusWagner.Steiner

theorem aux_sta_reach {V : Type*} (H : SimpleGraph V) (u v : V)
    (huv : (H.deleteEdges {s(u, v)}).Reachable u v) {x y : V} (h : H.Reachable x y) :
    (H.deleteEdges {s(u, v)}).Reachable x y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | @cons a b c hadj p ih =>
    refine SimpleGraph.Reachable.trans ?_ ih
    by_cases he : s(a, b) = s(u, v)
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact huv
      · exact huv.symm
    · exact SimpleGraph.Adj.reachable (by simp [SimpleGraph.deleteEdges_adj, hadj, he])

end DreyfusWagner.Steiner

open DreyfusWagner.Steiner

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) (hconn : G.Connected)
    (Y : Finset V) (S : Finset (Sym2 V)) (hS : IsSteinerTree G ℓ Y S) :
    (SimpleGraph.fromEdgeSet (S : Set (Sym2 V))).IsAcyclic := by
  classical
  by_contra hcyc
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge] at hcyc
  push Not at hcyc
  obtain ⟨u, v, hadj, hnb⟩ := hcyc
  rw [SimpleGraph.isBridge_iff, not_not] at hnb
  obtain ⟨hSG, hSc, hmin⟩ := hS
  have heS : s(u, v) ∈ S := by
    rw [SimpleGraph.fromEdgeSet_adj] at hadj
    exact_mod_cast hadj.1
  have hdel : (SimpleGraph.fromEdgeSet (S : Set (Sym2 V))).deleteEdges {s(u, v)} =
      SimpleGraph.fromEdgeSet ((S.erase s(u, v) : Finset (Sym2 V)) : Set (Sym2 V)) := by
    ext a b
    simp only [SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj, Finset.coe_erase,
      Set.mem_sdiff, Set.mem_singleton_iff, Finset.mem_coe]
    tauto
  have hconn' : Connects (S.erase s(u, v)) Y := by
    intro x hx y hy
    rw [← hdel]
    exact aux_sta_reach _ u v hnb (hSc x hx y hy)
  have hsub : S.erase s(u, v) ⊆ G.edgeFinset := (Finset.erase_subset _ _).trans hSG
  have hle := hmin _ hsub hconn'
  unfold arcLength at hle
  have heG : s(u, v) ∈ G.edgeSet := by
    have := hSG heS
    simpa using this
  have hp := hpos _ heG
  rw [← Finset.add_sum_erase S ℓ heS] at hle
  linarith
