-- Prove2me | solution 1 for Erdos180.proposedFamilyFree_sixteenth_power_host_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T03:20:11.100984+00:00
-- url     : https://prove2.me/submissions/3bd69d3c-30c8-49bf-8475-2e6e98c722b2

import Definitions.Def_erdos180_core4
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Order.CompletePartialOrder
import Theorems.Thm_Erdos180_booleanCut_adj
import Theorems.Thm_Erdos180_degree_eq_natCard_neighborSet
import Theorems.Thm_Erdos180_edgeFinset_card_eq_natCard
import Theorems.Thm_Erdos180_flipBooleanColor_self
import Theorems.Thm_Erdos180_proposedFamilyFree_minDegree_ambient_sixteenth_power_le

namespace Erdos180

noncomputable section
open Finset SimpleGraph
open scoped Classical

lemma booleanCut_le {V : Type*} (G : SimpleGraph V)
    (color : V → Bool) : booleanCut G color ≤ G := by
  intro u v huv
  exact huv.1

lemma booleanCut_isBipartite {V : Type*} (G : SimpleGraph V)
    (color : V → Bool) : (booleanCut G color).IsBipartite := by
  simpa using (SimpleGraph.Coloring.mk
    (G := booleanCut G color) color (fun h => h.2)).colorable

lemma booleanCut_deleteIncidence_flip
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (color : V → Bool) (v : V) :
    (booleanCut G (flipBooleanColor color v)).deleteIncidenceSet v =
      (booleanCut G color).deleteIncidenceSet v := by
  ext x y
  simp only [SimpleGraph.deleteIncidenceSet_adj, booleanCut_adj]
  by_cases hx : x = v
  · subst x
    simp
  by_cases hy : y = v
  · subst y
    simp
  simp [flipBooleanColor, hx, hy]

lemma booleanCut_flip_neighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool) (v : V) :
    (booleanCut G (flipBooleanColor color v)).neighborFinset v =
      G.neighborFinset v \ (booleanCut G color).neighborFinset v := by
  classical
  ext w
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_sdiff,
    booleanCut_adj]
  by_cases hwv : w = v
  · subst w
    simp
  · cases hcv : color v <;> cases hcw : color w <;>
      simp [flipBooleanColor, hwv, hcv, hcw]

lemma booleanCut_flip_degree_add
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool) (v : V) :
    (booleanCut G (flipBooleanColor color v)).degree v +
        (booleanCut G color).degree v = G.degree v := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree,
      booleanCut_flip_neighborFinset]
  apply Finset.card_sdiff_add_card_eq_card
  intro w hw
  have hadj : (booleanCut G color).Adj v w := by
    simpa only [SimpleGraph.mem_neighborFinset] using hw
  simpa only [SimpleGraph.mem_neighborFinset] using hadj.1

theorem exists_maximum_booleanCut
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ color : V → Bool, ∀ other : V → Bool,
      (booleanCut G other).edgeFinset.card ≤
        (booleanCut G color).edgeFinset.card := by
  classical
  obtain ⟨color, _, hcolor⟩ := Finset.exists_max_image
    (Finset.univ : Finset (V → Bool))
    (fun candidate => (booleanCut G candidate).edgeFinset.card)
    (Finset.univ_nonempty)
  exact ⟨color, fun other => hcolor other (Finset.mem_univ other)⟩

lemma maximum_booleanCut_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool)
    (hmax : ∀ other : V → Bool,
      (booleanCut G other).edgeFinset.card ≤
        (booleanCut G color).edgeFinset.card)
    (v : V) :
    G.degree v ≤ 2 * (booleanCut G color).degree v := by
  classical
  let flipped := flipBooleanColor color v
  have hflipped := hmax flipped
  have hdeleted := congrArg (fun H : SimpleGraph V => Nat.card H.edgeSet)
    (booleanCut_deleteIncidence_flip G color v)
  have hedge :
      (booleanCut G flipped).edgeFinset.card -
          (booleanCut G flipped).degree v =
        (booleanCut G color).edgeFinset.card -
          (booleanCut G color).degree v := by
    calc
      (booleanCut G flipped).edgeFinset.card -
          (booleanCut G flipped).degree v =
        ((booleanCut G flipped).deleteIncidenceSet v).edgeFinset.card :=
        (SimpleGraph.card_edgeFinset_deleteIncidenceSet
          (booleanCut G flipped) v).symm
      _ = Nat.card ((booleanCut G flipped).deleteIncidenceSet v).edgeSet :=
        edgeFinset_card_eq_natCard _
      _ = Nat.card ((booleanCut G color).deleteIncidenceSet v).edgeSet :=
        hdeleted
      _ = ((booleanCut G color).deleteIncidenceSet v).edgeFinset.card :=
        (edgeFinset_card_eq_natCard _).symm
      _ = (booleanCut G color).edgeFinset.card -
          (booleanCut G color).degree v :=
        SimpleGraph.card_edgeFinset_deleteIncidenceSet
          (booleanCut G color) v
  have hflipDegree :=
    SimpleGraph.degree_le_card_edgeFinset (booleanCut G flipped) v
  have hcutDegree :=
    SimpleGraph.degree_le_card_edgeFinset (booleanCut G color) v
  have hpartition := booleanCut_flip_degree_add G color v
  change (booleanCut G flipped).degree v +
    (booleanCut G color).degree v = G.degree v at hpartition
  omega

theorem exists_bipartite_half_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ B : SimpleGraph V,
      B.IsBipartite ∧ B ≤ G ∧
      G.edgeFinset.card ≤ 2 * B.edgeFinset.card := by
  classical
  obtain ⟨color, hmax⟩ := exists_maximum_booleanCut G
  refine ⟨booleanCut G color, booleanCut_isBipartite G color,
    booleanCut_le G color, ?_⟩
  have hsum :
      2 * G.edgeFinset.card ≤
        2 * (2 * (booleanCut G color).edgeFinset.card) := by
    calc
      2 * G.edgeFinset.card = ∑ v : V, G.degree v :=
        (SimpleGraph.sum_degrees_eq_twice_card_edges G).symm
      _ ≤ ∑ v : V, 2 * (booleanCut G color).degree v :=
        Finset.sum_le_sum fun v _ =>
          maximum_booleanCut_degree G color hmax v
      _ = 2 * (2 * (booleanCut G color).edgeFinset.card) := by
        rw [← Finset.mul_sum,
          SimpleGraph.sum_degrees_eq_twice_card_edges]
  have hhalf := Nat.le_of_mul_le_mul_left hsum (by omega)
  simpa only [edgeFinset_card_eq_natCard] using hhalf

lemma natCard_support_le_card
    {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Nat.card G.support ≤ Fintype.card V := by
  simpa only [Nat.card_eq_fintype_card] using
    (Finite.card_subtype_le (fun v : V => v ∈ G.support))

lemma natCard_support_deleteIncidence_add_one_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {v : V} (hv : v ∈ G.support) :
    Nat.card (G.deleteIncidenceSet v).support + 1 ≤
      Nat.card G.support := by
  have hdrop := SimpleGraph.card_support_deleteIncidenceSet G hv
  have hpositive : 0 < Nat.card G.support :=
    Finite.card_pos_iff.mpr ⟨⟨v, hv⟩⟩
  simp only [Nat.card_eq_fintype_card] at hpositive ⊢
  omega

theorem exists_maximum_sharp_pruning_subgraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (base : SimpleGraph V) (originalEdges : ℕ) :
    ∃ H : SimpleGraph V, H ≤ base ∧
      (∀ D : SimpleGraph V, D ≤ base →
        sharpPruningPotential originalEdges D ≤
          sharpPruningPotential originalEdges H) ∧
      (∀ D : SimpleGraph V, D ≤ base →
        sharpPruningScore originalEdges D ≤
          sharpPruningScore originalEdges H) := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun H : SimpleGraph V => H ≤ base)
  have hnonempty : candidates.Nonempty := by
    refine ⟨⊥, ?_⟩
    simp [candidates]
  obtain ⟨H, hH, hmax⟩ := Finset.exists_max_image
    candidates (sharpPruningScore originalEdges) hnonempty
  refine ⟨H, (Finset.mem_filter.mp hH).2, ?_, ?_⟩
  · intro D hD
    have hscore := hmax D
      (Finset.mem_filter.mpr ⟨Finset.mem_univ D, hD⟩)
    unfold sharpPruningScore at hscore
    split_ifs at hscore <;> omega
  · intro D hD
    exact hmax D
      (Finset.mem_filter.mpr ⟨Finset.mem_univ D, hD⟩)

lemma maximum_sharp_pruning_subgraph_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (base H : SimpleGraph V) [DecidableRel H.Adj]
    (originalEdges : ℕ) (hHB : H ≤ base)
    (hmax : ∀ D : SimpleGraph V, D ≤ base →
      sharpPruningPotential originalEdges D ≤
        sharpPruningPotential originalEdges H)
    {v : V} (hv : v ∈ H.support) :
    originalEdges ≤ 2 * Fintype.card V * H.degree v := by
  classical
  let D := H.deleteIncidenceSet v
  have hDB : D ≤ base :=
    le_trans (SimpleGraph.deleteIncidenceSet_le H v) hHB
  have hscore := hmax D hDB
  have hdrop : Nat.card D.support + 1 ≤ Nat.card H.support :=
    natCard_support_deleteIncidence_add_one_le H hv
  have hsupport : Nat.card H.support ≤ Fintype.card V :=
    natCard_support_le_card H
  have hcomplement :
      Fintype.card V - Nat.card H.support + 1 ≤
        Fintype.card V - Nat.card D.support := by
    omega
  have hweightedComplement :
      originalEdges * (Fintype.card V - Nat.card H.support) +
          originalEdges ≤
        originalEdges * (Fintype.card V - Nat.card D.support) := by
    calc
      originalEdges * (Fintype.card V - Nat.card H.support) +
          originalEdges =
        originalEdges * (Fintype.card V - Nat.card H.support + 1) := by
          simp [Nat.mul_add]
      _ ≤ originalEdges * (Fintype.card V - Nat.card D.support) :=
        Nat.mul_le_mul_left originalEdges hcomplement
  have hdeleted :
      Nat.card D.edgeSet =
        Nat.card H.edgeSet - Nat.card (H.neighborSet v) := by
    simpa only [D, edgeFinset_card_eq_natCard,
      degree_eq_natCard_neighborSet] using
      (SimpleGraph.card_edgeFinset_deleteIncidenceSet H v)
  have hdegreeEdges :
      Nat.card (H.neighborSet v) ≤ Nat.card H.edgeSet := by
    simpa only [edgeFinset_card_eq_natCard,
      degree_eq_natCard_neighborSet] using
      (SimpleGraph.degree_le_card_edgeFinset H v)
  have hedgeAdd :
      Nat.card D.edgeSet + Nat.card (H.neighborSet v) =
        Nat.card H.edgeSet := by
    omega
  have hweightedEdges :
      2 * Fintype.card V * Nat.card H.edgeSet =
        2 * Fintype.card V * Nat.card D.edgeSet +
          2 * Fintype.card V * Nat.card (H.neighborSet v) := by
    rw [← hedgeAdd, mul_add]
  change
    2 * Fintype.card V * Nat.card D.edgeSet +
        originalEdges * (Fintype.card V - Nat.card D.support) ≤
      2 * Fintype.card V * Nat.card H.edgeSet +
        originalEdges * (Fintype.card V - Nat.card H.support)
    at hscore
  simp only [degree_eq_natCard_neighborSet]
  omega

lemma maximum_sharp_pruning_subgraph_edge_positive
    {V : Type*} [Fintype V] [DecidableEq V]
    (original base H : SimpleGraph V) [DecidableRel original.Adj]
    (hpositive : 0 < original.edgeFinset.card)
    (hhalf : original.edgeFinset.card ≤ 2 * base.edgeFinset.card)
    (hmax : ∀ D : SimpleGraph V, D ≤ base →
      sharpPruningScore (Nat.card original.edgeSet) D ≤
        sharpPruningScore (Nat.card original.edgeSet) H) :
    0 < Nat.card H.edgeSet := by
  classical
  have hpositiveNat : 0 < Nat.card original.edgeSet := by
    simpa only [edgeFinset_card_eq_natCard] using hpositive
  have hhalfNat :
      Nat.card original.edgeSet ≤ 2 * Nat.card base.edgeSet := by
    simpa only [edgeFinset_card_eq_natCard] using hhalf
  have hbasePositive : 0 < Nat.card base.edgeSet := by
    omega
  have hbaseScore := hmax base (le_refl base)
  by_contra hnot
  have hHzero : Nat.card H.edgeSet = 0 := by
    omega
  have hHedge : H.edgeFinset.card = 0 := by
    simpa only [edgeFinset_card_eq_natCard] using hHzero
  have hHbot : H = ⊥ := by
    apply SimpleGraph.edgeFinset_eq_empty.mp
    exact Finset.card_eq_zero.mp hHedge
  have hsharpBase :
      Nat.card original.edgeSet * Fintype.card V ≤
        sharpPruningPotential (Nat.card original.edgeSet) base := by
    have hcross :
        Nat.card original.edgeSet * Fintype.card V ≤
          2 * Fintype.card V * Nat.card base.edgeSet := by
      calc
        Nat.card original.edgeSet * Fintype.card V =
            Fintype.card V * Nat.card original.edgeSet := by
          ac_rfl
        _ ≤ Fintype.card V * (2 * Nat.card base.edgeSet) :=
          Nat.mul_le_mul_left (Fintype.card V) hhalfNat
        _ = 2 * Fintype.card V * Nat.card base.edgeSet := by
          ac_rfl
    unfold sharpPruningPotential
    omega
  have hHscore :
      sharpPruningScore (Nat.card original.edgeSet) H =
        2 * (Nat.card original.edgeSet * Fintype.card V) := by
    rw [hHbot]
    simp [sharpPruningScore, sharpPruningPotential]
  have hscoreContradiction :
      2 * sharpPruningPotential (Nat.card original.edgeSet) base + 1 ≤
        2 * (Nat.card original.edgeSet * Fintype.card V) := by
    calc
      2 * sharpPruningPotential (Nat.card original.edgeSet) base + 1 =
          sharpPruningScore (Nat.card original.edgeSet) base := by
        unfold sharpPruningScore
        rw [if_pos hbasePositive]
      _ ≤ sharpPruningScore (Nat.card original.edgeSet) H :=
        hbaseScore
      _ = 2 * (Nat.card original.edgeSet * Fintype.card V) :=
        hHscore
  omega

theorem exists_bipartite_min_degree_supported_subgraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hpositive : 0 < G.edgeFinset.card) :
    ∃ H : SimpleGraph V,
      H.IsBipartite ∧ H ≤ G ∧ 0 < Nat.card H.edgeSet ∧
      ∀ v : V, v ∈ H.support →
        G.edgeFinset.card ≤ 2 * Fintype.card V * H.degree v := by
  classical
  obtain ⟨cut, hcutBipartite, hcutSubgraph, hcutEdges⟩ :=
    exists_bipartite_half_edges G
  obtain ⟨H, hH, hpotential, hscore⟩ :=
    exists_maximum_sharp_pruning_subgraph cut (Nat.card G.edgeSet)
  refine ⟨H, SimpleGraph.Colorable.mono_left hH hcutBipartite,
    le_trans hH hcutSubgraph,
    maximum_sharp_pruning_subgraph_edge_positive
      G cut H hpositive hcutEdges hscore, ?_⟩
  intro v hv
  simpa only [edgeFinset_card_eq_natCard,
    degree_eq_natCard_neighborSet] using
    (maximum_sharp_pruning_subgraph_degree
      cut H (Nat.card G.edgeSet) hH hpotential hv)

theorem exists_bipartite_min_degree_subgraph
    {n : ℕ} (G : SimpleGraph (Fin n))
    (hpositive : 0 < G.edgeFinset.card) :
    ∃ (N : ℕ) (B : SimpleGraph (Fin N)) (f : Fin N ↪ Fin n),
      0 < N ∧ N ≤ n ∧ B.IsBipartite ∧ B.map f ≤ G ∧
      G.edgeFinset.card ≤ 2 * n * B.minDegree ∧
      ∀ v : Fin N, G.edgeFinset.card ≤ 2 * n * B.degree v := by
  classical
  obtain ⟨H, hHbip, hHG, hHpositive, hminimum⟩ :=
    exists_bipartite_min_degree_supported_subgraph G hpositive
  have hsupportPositive : 0 < Nat.card H.support := by
    apply Finite.card_pos_iff.mpr
    obtain ⟨⟨edge, hedge⟩⟩ := Finite.card_pos_iff.mp hHpositive
    induction edge using Sym2.inductionOn with
    | hf u v =>
      have huv : H.Adj u v := by
        simpa only [SimpleGraph.mem_edgeSet] using hedge
      exact ⟨⟨u, huv.mem_support_left⟩⟩
  let N := Nat.card H.support
  let supportEquiv : Fin N ≃ H.support :=
    (Finite.equivFin H.support).symm
  let f : Fin N ↪ Fin n :=
    supportEquiv.toEmbedding.trans
      (Function.Embedding.subtype (fun v : Fin n => v ∈ H.support))
  let B : SimpleGraph (Fin N) :=
    (H.induce H.support).comap supportEquiv.toEmbedding
  have hBcomap : B = H.comap f := by
    ext u v
    rfl
  have hBbip : B.IsBipartite := by
    rw [hBcomap]
    exact SimpleGraph.Colorable.of_hom
      (SimpleGraph.Hom.comap f H) hHbip
  have hmap : B.map f ≤ G := by
    calc
      B.map f ≤ H := by
        rw [hBcomap]
        exact SimpleGraph.map_comap_le f H
      _ ≤ G := hHG
  let supportIso : B ≃g H.induce H.support :=
    SimpleGraph.Iso.comap supportEquiv (H.induce H.support)
  have hdegrees : ∀ v : Fin N,
      G.edgeFinset.card ≤ 2 * n * B.degree v := by
    intro v
    have hdegree := hminimum (f v) (supportEquiv v).property
    have hBdegree :
        Nat.card (B.neighborSet v) =
          Nat.card (H.neighborSet (f v)) := by
      calc
        Nat.card (B.neighborSet v) =
            Nat.card ((H.induce H.support).neighborSet
              (supportEquiv v)) := by
          change Nat.card (B.neighborSet v) =
            Nat.card ((H.induce H.support).neighborSet (supportIso v))
          exact Nat.card_congr (supportIso.mapNeighborSet v)
        _ = Nat.card (H.neighborSet (f v)) := by
          change Nat.card ((H.induce H.support).neighborSet
            (supportEquiv v)) =
              Nat.card (H.neighborSet (supportEquiv v : Fin n))
          simpa only [degree_eq_natCard_neighborSet] using
            (SimpleGraph.degree_induce_support (G := H)
              (supportEquiv v))
    simpa only [edgeFinset_card_eq_natCard,
      degree_eq_natCard_neighborSet, Fintype.card_fin, hBdegree]
      using hdegree
  have hNn : N ≤ n := by
    simpa using Fintype.card_le_of_injective f f.injective
  letI : Nonempty (Fin N) := ⟨⟨0, hsupportPositive⟩⟩
  obtain ⟨v, hv⟩ := B.exists_minimal_degree_vertex
  have hmin : G.edgeFinset.card ≤ 2 * n * B.minDegree := by
    rw [hv]
    exact hdegrees v
  exact ⟨N, B, f, hsupportPositive, hNn,
    hBbip, hmap, hmin, hdegrees⟩

end

noncomputable section
open Filter Finset SimpleGraph
open scoped Classical Topology

lemma familyFree_of_embedded_subgraph
    {family : Finset FiniteGraph}
    {n N : ℕ} (host : SimpleGraph (Fin n))
    (subgraph : SimpleGraph (Fin N))
    (embedding : Fin N ↪ Fin n)
    (hsub : subgraph.map embedding ≤ host)
    (hfree : FamilyFree family host) :
    FamilyFree family subgraph := by
  intro forbidden hforbidden hcontained
  exact hfree forbidden hforbidden
    ((hcontained.trans
      ⟨(SimpleGraph.Embedding.map embedding subgraph).toCopy⟩).mono_right hsub)

end

end Erdos180

open Erdos180
open Filter Finset SimpleGraph
open scoped Classical Topology

theorem solution
    (n : ℕ) (host : SimpleGraph (Fin n))
    (hfree : FamilyFree proposedFamily host) :
    (host.edgeFinset.card : ℝ) ^ 16 ≤
      compactnessHostPowerConstant * (n : ℝ) ^ 21 := by
  classical
  by_cases hzero : host.edgeFinset.card = 0
  · simp only [hzero, Nat.cast_zero, zero_pow (by norm_num : 16 ≠ 0)]
    unfold compactnessHostPowerConstant compactnessDegreePowerConstant
    positivity
  · have hpositive : 0 < host.edgeFinset.card :=
      Nat.pos_of_ne_zero hzero
    obtain ⟨N, B, f, hN, hNn, hBbip, hmap, hminimum,
      _hminimum_pointwise⟩ :=
      exists_bipartite_min_degree_subgraph host hpositive
    have hn : 0 < n := by
      omega
    have hBfree : FamilyFree proposedFamily B :=
      familyFree_of_embedded_subgraph host B f hmap hfree
    let d : ℕ := B.minDegree
    have hdegree : ∀ v : Fin N, d ≤ B.degree v := by
      intro v
      exact B.minDegree_le_degree v
    have hminimumNat :
        host.edgeFinset.card ≤ 2 * n * d := by
      simpa only [d] using hminimum
    have hminimumReal :
        (host.edgeFinset.card : ℝ) ≤
          2 * (n : ℝ) * (d : ℝ) := by
      exact_mod_cast hminimumNat
    have hdPower := proposedFamilyFree_minDegree_ambient_sixteenth_power_le
      B hN hn hNn hBfree hBbip d hdegree
    calc
      (host.edgeFinset.card : ℝ) ^ 16 ≤
          (2 * (n : ℝ) * (d : ℝ)) ^ 16 := by
        gcongr
      _ = (2 : ℝ) ^ 16 * (n : ℝ) ^ 16 * (d : ℝ) ^ 16 := by
        ring
      _ ≤ (2 : ℝ) ^ 16 * (n : ℝ) ^ 16 *
          (compactnessDegreePowerConstant * (n : ℝ) ^ 5) := by
        gcongr
      _ = compactnessHostPowerConstant * (n : ℝ) ^ 21 := by
        unfold compactnessHostPowerConstant
        ring
