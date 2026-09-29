-- Prove2me | solution 1 for DreyfusWagner.Steiner.steinerLength_pair_eq_pathDist
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:44:34.330983+00:00
-- url     : https://prove2.me/submissions/13ccb6ce-4960-4454-a047-f4d974627b65

import Mathlib
import Definitions.Def_DreyfusWagner_Steiner_SteinerProblem

namespace DreyfusWagner.Steiner

end DreyfusWagner.Steiner

open DreyfusWagner.Steiner

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) (hconn : G.Connected) (i j : V) :
    steinerLength G ℓ {i, j} = pathDist G ℓ i j := by
  classical
  apply le_antisymm
  · -- every path gives an arc set connecting {i, j} of the same length
    unfold pathDist
    apply Finset.le_inf
    intro n _
    apply Finset.le_inf
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨_, hpath⟩ := hp
    have hnodup : p.edges.Nodup := hpath.isTrail.edges_nodup
    unfold steinerLength
    calc _ ≤ ((arcLength ℓ p.edges.toFinset : ℝ) : WithTop ℝ) := by
          apply Finset.inf_le
          rw [Finset.mem_filter, Finset.mem_powerset]
          refine ⟨?_, ?_⟩
          · intro e he
            rw [List.mem_toFinset] at he
            rw [SimpleGraph.mem_edgeFinset]
            exact p.edges_subset_edgeSet he
          · have hsub : ∀ e, e ∈ p.edges →
                e ∈ (SimpleGraph.fromEdgeSet ((p.edges.toFinset : Finset (Sym2 V)) :
                  Set (Sym2 V))).edgeSet := by
              intro e he
              rw [SimpleGraph.edgeSet_fromEdgeSet]
              refine ⟨?_, ?_⟩
              · simpa using he
              · rw [Sym2.mem_diagSet]
                exact G.not_isDiag_of_mem_edgeSet (p.edges_subset_edgeSet he)
            have hij : (SimpleGraph.fromEdgeSet ((p.edges.toFinset : Finset (Sym2 V)) :
                  Set (Sym2 V))).Reachable i j := ⟨p.transfer _ hsub⟩
            intro x hx y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
            · exact SimpleGraph.Reachable.refl _
            · exact hij
            · exact hij.symm
            · exact SimpleGraph.Reachable.refl _
      _ = _ := by
          unfold arcLength
          rw [List.sum_toFinset _ hnodup]
  · -- every connecting arc set contains a path from i to j
    unfold steinerLength
    apply Finset.le_inf
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hSG, hSc⟩ := hS
    have hr : (SimpleGraph.fromEdgeSet (S : Set (Sym2 V))).Reachable i j :=
      hSc i (by simp) j (by simp)
    obtain ⟨w⟩ := hr
    have hle : SimpleGraph.fromEdgeSet (S : Set (Sym2 V)) ≤ G := by
      intro a b hab
      rw [SimpleGraph.fromEdgeSet_adj] at hab
      have := hSG (by simpa using hab.1 : s(a, b) ∈ S)
      rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
    have hpath : (w.bypass.mapLe hle).IsPath := (w.bypass_isPath).mapLe hle
    unfold pathDist
    calc _ ≤ ((((w.bypass.mapLe hle).edges.map ℓ).sum : ℝ) : WithTop ℝ) := by
          refine (Finset.inf_le (Finset.mem_range.mpr hpath.length_lt)).trans ?_
          apply Finset.inf_le
          rw [Finset.mem_filter]
          exact ⟨(SimpleGraph.mem_finsetWalkLength_iff).mpr rfl, hpath⟩
      _ ≤ _ := by
          rw [WithTop.coe_le_coe]
          rw [← List.sum_toFinset _ hpath.isTrail.edges_nodup]
          unfold arcLength
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro e he
            rw [List.mem_toFinset, SimpleGraph.Walk.edges_mapLe_eq_edges] at he
            have h1 := (w.bypass).edges_subset_edgeSet he
            rw [SimpleGraph.edgeSet_fromEdgeSet] at h1
            exact_mod_cast h1.1
          · intro e he _
            have := hSG he
            rw [SimpleGraph.mem_edgeFinset] at this
            exact (hpos e this).le
