-- Prove2me | solution 1 for Erdos146.eventually_expectedRetainedEdge_le_extremalNumber
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:50:22.538879+00:00
-- url     : https://prove2.me/submissions/019e9a65-e4c8-4a6f-8120-450939b64102

import Definitions.Def_erdos146_core2
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.InformationTheory.Hamming
import Theorems.Thm_Erdos146_CompactnessConjecture_free_map_of_no_isolated
import Theorems.Thm_Erdos146_eventually_exists_pairGraph_free_dense_retainedHost
import Theorems.Thm_Erdos146_hammingHost_adj_iff
import Theorems.Thm_Erdos146_pairGraphOverFin_forall_exists_adj

namespace Erdos146

section
open Filter Finset SimpleGraph
open scoped Topology

open Classical in
theorem hammingRetainedVertexCount_eq_card
    (dimension : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    hammingRetainedVertexCount dimension retained =
      (Fintype.card retained : ℝ) := by
  classical
  simp [hammingRetainedVertexCount, Fintype.card_subtype]

theorem hammingRetainedEdgeCount_eq_wordEdges_card
    (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    hammingRetainedEdgeCount dimension radius retained =
      ((retainedHammingWordEdges dimension radius retained).card : ℝ) := by
  classical
  unfold hammingRetainedEdgeCount
  calc
    (∑ left : HammingWord dimension,
      ∑ right : HammingWord dimension,
        if hammingDist left right ≤ radius ∧
            (false, left) ∈ retained ∧ (true, right) ∈ retained
        then (1 : ℝ) else 0) =
      ∑ edge : HammingWord dimension × HammingWord dimension,
        if hammingDist edge.1 edge.2 ≤ radius ∧
            (false, edge.1) ∈ retained ∧ (true, edge.2) ∈ retained
        then (1 : ℝ) else 0 := by
          rw [Fintype.sum_prod_type]
    _ = ∑ _edge ∈ retainedHammingWordEdges dimension radius retained,
          (1 : ℝ) := by
      unfold retainedHammingWordEdges
      rw [← Finset.sum_filter]
    _ = ((retainedHammingWordEdges dimension radius retained).card : ℝ) := by
      simp

open Classical in
theorem retainedHammingHost_edgeFinset_card
    (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    (retainedHammingHost dimension radius retained).edgeFinset.card =
      (retainedHammingWordEdges dimension radius retained).card := by
  classical
  let toEdge :
      ∀ edge ∈ retainedHammingWordEdges dimension radius retained,
        Sym2 retained := fun edge hedge =>
    s(⟨(false, edge.1), by
        exact (Finset.mem_filter.mp hedge).2.2.1⟩,
      ⟨(true, edge.2), by
        exact (Finset.mem_filter.mp hedge).2.2.2⟩)
  have hcard :
      (retainedHammingWordEdges dimension radius retained).card =
        (retainedHammingHost dimension radius retained).edgeFinset.card := by
    apply Finset.card_bij toEdge
    · intro edge hedge
      have hdata := (Finset.mem_filter.mp hedge).2
      change
        s(⟨(false, edge.1), hdata.2.1⟩,
          ⟨(true, edge.2), hdata.2.2⟩) ∈
          (retainedHammingHost dimension radius retained).edgeFinset
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      change (hammingHost dimension radius).Adj
        (false, edge.1) (true, edge.2)
      apply (hammingHost_adj_iff dimension radius _ _).mpr
      exact ⟨by simp, hdata.1⟩
    · intro first hfirst second hsecond hequal
      dsimp [toEdge] at hequal
      rcases (Sym2.eq_iff.mp hequal) with
        ⟨hleft, hright⟩ | ⟨hswap, _⟩
      · apply Prod.ext
        · exact congrArg (fun vertex : retained => vertex.val.2) hleft
        · exact congrArg (fun vertex : retained => vertex.val.2) hright
      · have hside :=
          congrArg (fun vertex : retained => vertex.val.1) hswap
        simp at hside
    · intro edge hedge
      induction edge using Sym2.inductionOn with
      | hf first second =>
        have hadj :
            (retainedHammingHost dimension radius retained).Adj
              first second := by
          exact (SimpleGraph.mem_edgeSet
            (retainedHammingHost dimension radius retained)).mp
              ((SimpleGraph.mem_edgeFinset).mp hedge)
        have hhost :
            (hammingHost dimension radius).Adj
              first.val second.val := hadj
        rcases first with ⟨⟨firstSide, firstWord⟩, hfirst⟩
        rcases second with ⟨⟨secondSide, secondWord⟩, hsecond⟩
        have hdata :=
          (hammingHost_adj_iff dimension radius
            (firstSide, firstWord) (secondSide, secondWord)).mp hhost
        cases firstSide <;> cases secondSide
        · simp at hdata
        · refine ⟨(firstWord, secondWord), ?_, ?_⟩
          · unfold retainedHammingWordEdges
            simp [hdata.2, hfirst, hsecond]
          · simp [toEdge]
        · have hreverse : hammingDist secondWord firstWord ≤ radius := by
            simpa [hammingDist_comm] using hdata.2
          refine ⟨(secondWord, firstWord), ?_, ?_⟩
          · unfold retainedHammingWordEdges
            simp [hreverse, hfirst, hsecond]
          · dsimp [toEdge]
            exact Sym2.eq_swap
        · simp at hdata
  exact hcard.symm

open Classical in
theorem hammingRetainedEdgeCount_eq_edgeFinset_card
    (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    hammingRetainedEdgeCount dimension radius retained =
      ((retainedHammingHost dimension radius retained).edgeFinset.card : ℝ) := by
  rw [hammingRetainedEdgeCount_eq_wordEdges_card,
    retainedHammingHost_edgeFinset_card]

open Classical in
theorem retainedVertex_card_le_manuscriptVertexCount
    (dimension : ℕ)
    (retained : Set (Bool × HammingWord dimension))
    (hvertices :
      hammingRetainedVertexCount dimension retained <
        3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)) :
    Fintype.card retained ≤ manuscriptVertexCount dimension := by
  have hreal :
      (Fintype.card retained : ℝ) ≤
        (manuscriptVertexCount dimension : ℝ) := by
    calc
      (Fintype.card retained : ℝ) =
          hammingRetainedVertexCount dimension retained :=
        (hammingRetainedVertexCount_eq_card dimension retained).symm
      _ ≤ 3 * hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ) := hvertices.le
      _ ≤ (⌈3 * hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ)⌉₊ : ℝ) :=
        Nat.le_ceil _
      _ = (manuscriptVertexCount dimension : ℝ) := rfl
  exact_mod_cast hreal

end

end Erdos146

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

open Classical in
theorem solution :
    ∃ baseSize depth : ℕ,
      4 ≤ baseSize ∧
      0 < depth ∧
      1 < (depth : ℝ) * (certifiedWindowWidth / 2) ∧
      ∀ᶠ dimension : ℕ in Filter.atTop,
        hammingExpectedRetainedEdgeCount dimension
            (manuscriptHammingRadius dimension) / 2 ≤
          (SimpleGraph.extremalNumber
            (manuscriptVertexCount dimension)
            (pairGraphOverFin baseSize depth) : ℝ) := by
  obtain ⟨baseSize, depth, hbase, hdepth,
    hdepth_window, hhosts⟩ :=
    eventually_exists_pairGraph_free_dense_retainedHost
  refine ⟨baseSize, depth, hbase, hdepth, hdepth_window, ?_⟩
  filter_upwards [hhosts] with dimension hhost
  obtain ⟨retained, hfree, hvertices, hedges⟩ := hhost
  have hcard :=
    retainedVertex_card_le_manuscriptVertexCount
      dimension retained hvertices
  have hembedding :
      Nonempty (retained ↪ Fin (manuscriptVertexCount dimension)) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa using hcard
  obtain ⟨embedding⟩ := hembedding
  let paddedHost : SimpleGraph (Fin (manuscriptVertexCount dimension)) :=
    (retainedHammingHost dimension
      (manuscriptHammingRadius dimension) retained).map embedding
  have hpadded_free :
      (pairGraphOverFin baseSize depth).Free paddedHost := by
    exact CompactnessConjecture.free_map_of_no_isolated
      (pairGraphOverFin baseSize depth)
      (pairGraphOverFin_forall_exists_adj baseSize depth hbase hdepth)
      embedding hfree
  have hpadded_edges :
      paddedHost.edgeFinset.card ≤
        SimpleGraph.extremalNumber
          (manuscriptVertexCount dimension)
          (pairGraphOverFin baseSize depth) := by
    simpa using
      (SimpleGraph.card_edgeFinset_le_extremalNumber hpadded_free)
  calc
    hammingExpectedRetainedEdgeCount dimension
        (manuscriptHammingRadius dimension) / 2 ≤
      hammingRetainedEdgeCount dimension
        (manuscriptHammingRadius dimension) retained := hedges
    _ = ((retainedHammingHost dimension
        (manuscriptHammingRadius dimension) retained).edgeFinset.card : ℝ) :=
      hammingRetainedEdgeCount_eq_edgeFinset_card
        dimension (manuscriptHammingRadius dimension) retained
    _ = (paddedHost.edgeFinset.card : ℝ) := by
      congr 1
      exact (SimpleGraph.card_edgeFinset_map embedding
        (retainedHammingHost dimension
          (manuscriptHammingRadius dimension) retained)).symm
    _ ≤ (SimpleGraph.extremalNumber
        (manuscriptVertexCount dimension)
        (pairGraphOverFin baseSize depth) : ℝ) := by
      exact_mod_cast hpadded_edges
