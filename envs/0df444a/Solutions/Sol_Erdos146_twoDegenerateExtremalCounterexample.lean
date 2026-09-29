-- Prove2me | solution 1 for Erdos146.twoDegenerateExtremalCounterexample
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:53:39.761841+00:00
-- url     : https://prove2.me/submissions/aa5c8fbc-c9a3-47dd-a4ed-f31a191ed0ea

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Theorems.Thm_Erdos146_CompactnessConjecture_free_map_of_no_isolated
import Theorems.Thm_Erdos146_ParentSystem_graph_adj_iff
import Theorems.Thm_Erdos146_entropyUpperEndpoint_lt_one
import Theorems.Thm_Erdos146_eventually_manuscriptVertexCount_power_le_extremalNumber
import Theorems.Thm_Erdos146_exponentGain_pos
import Theorems.Thm_Erdos146_hammingRetentionProbability_mul_wordCount_eq_exp
import Theorems.Thm_Erdos146_hammingRetentionProbability_mul_wordCount_tendsto_atTop
import Theorems.Thm_Erdos146_manuscriptExtremalPower_pos
import Theorems.Thm_Erdos146_pairGraphOverFin_connected
import Theorems.Thm_Erdos146_pairGraphOverFin_forall_exists_adj
import Theorems.Thm_Erdos146_pairGraph_parent_child_adj

namespace Erdos146

namespace CompactnessConjecture
noncomputable section
open SimpleGraph

lemma extremalNumber_monotone_of_no_isolated
    {U : Type*} (forbidden : SimpleGraph U)
    (hneighbors : ∀ u : U, ∃ v : U, forbidden.Adj u v)
    {m n : ℕ} (hmn : m ≤ n) :
    SimpleGraph.extremalNumber m forbidden ≤
      SimpleGraph.extremalNumber n forbidden := by
  classical
  have hbound :
      SimpleGraph.extremalNumber (Fintype.card (Fin m)) forbidden ≤
        SimpleGraph.extremalNumber n forbidden := by
    apply (SimpleGraph.extremalNumber_le_iff
      (V := Fin m) forbidden
      (SimpleGraph.extremalNumber n forbidden)).mpr
    intro host _ hfree
    let embedding : Fin m ↪ Fin n := Fin.castLEEmb hmn
    have hpadded : forbidden.Free (host.map embedding) :=
      free_map_of_no_isolated forbidden hneighbors embedding hfree
    calc
      host.edgeFinset.card =
          (host.map embedding).edgeFinset.card := by
        simpa only [SimpleGraph.edgeFinset_card,
          ← Nat.card_eq_fintype_card] using
          (SimpleGraph.card_edgeFinset_map embedding host).symm
      _ ≤ SimpleGraph.extremalNumber n forbidden := by
        simpa using SimpleGraph.card_edgeFinset_le_extremalNumber hpadded
  simpa using hbound

end
end CompactnessConjecture

section
open Filter Finset SimpleGraph
open scoped Topology

theorem isTwoDegenerate_of_iso {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (hG : IsTwoDegenerate G) :
    IsTwoDegenerate H := by
  classical
  intro s hs
  let t : Finset V := s.map e.symm.toEquiv.toEmbedding
  have ht : t.Nonempty := by
    obtain ⟨w, hw⟩ := hs
    refine ⟨e.symm w, ?_⟩
    exact Finset.mem_map.mpr ⟨w, hw, rfl⟩
  obtain ⟨v, hv, hcard⟩ := hG t ht
  refine ⟨e v, ?_, ?_⟩
  · change v ∈ s.map e.symm.toEquiv.toEmbedding at hv
    obtain ⟨w, hw, heq⟩ := Finset.mem_map.mp hv
    have hwv : w = e v := by
      apply e.symm.toEquiv.injective
      simpa using heq
    simpa [← hwv] using hw
  · have hneighbors :
        neighborsWithin H s (e v) =
          (neighborsWithin G t v).map e.toEquiv.toEmbedding := by
      ext w
      simp only [neighborsWithin, Finset.mem_filter, Finset.mem_map_equiv]
      have hmembership : e.symm w ∈ t ↔ w ∈ s := by
        change e.symm w ∈ s.map e.symm.toEquiv.toEmbedding ↔ w ∈ s
        constructor
        · intro hmember
          obtain ⟨u, hu, heq⟩ := Finset.mem_map.mp hmember
          have huw : u = w := e.symm.toEquiv.injective heq
          simpa [huw] using hu
        · intro hmember
          exact Finset.mem_map.mpr ⟨w, hmember, rfl⟩
      have hadjacency :
          G.Adj v (e.symm w) ↔ H.Adj (e v) w := by
        simpa using (e.map_rel_iff (a := v) (b := e.symm w)).symm
      exact (and_congr hmembership hadjacency).symm
    rw [hneighbors, Finset.card_map]
    exact hcard

theorem isBipartite_of_iso {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (hG : G.IsBipartite) : H.IsBipartite := by
  obtain ⟨coloring⟩ := hG
  exact ⟨coloring.comp e.symm.toHom⟩

end

namespace ParentSystem
section
open Filter Finset SimpleGraph
open scoped Topology

theorem graph_isBipartite {V : Type*} (P : ParentSystem V) :
    P.graph.IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk
    (fun v => (⟨P.level v % 2, by omega⟩ : Fin 2)) ?_⟩
  intro v u hadj
  apply Fin.ne_of_val_ne
  change P.level v % 2 ≠ P.level u % 2
  rcases (P.graph_adj_iff v u).mp hadj with ⟨_, huv | huv⟩
  · have hlevel := P.parent_level huv
    omega
  · have hlevel := P.parent_level huv
    omega

theorem graph_isTwoDegenerate {V : Type*} (P : ParentSystem V) :
    IsTwoDegenerate P.graph := by
  classical
  intro s hs
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image s P.level hs
  refine ⟨v, hv, ?_⟩
  have hsubset : neighborsWithin P.graph s v ⊆ P.parents v := by
    intro u hu
    have hus : u ∈ s ∧ P.graph.Adj v u := by
      simpa [neighborsWithin] using hu
    rcases (P.graph_adj_iff v u).mp hus.2 with ⟨_, hparent | hchild⟩
    · exact hparent
    · have hlevel := P.parent_level hchild
      have hle := hmax u hus.1
      omega
  exact (Finset.card_le_card hsubset).trans (P.parent_card v)

end
end ParentSystem

section
open Filter Finset SimpleGraph
open scoped Topology

theorem pairGraph_isBipartite (baseSize depth : ℕ) :
    (pairParentSystem baseSize depth).graph.IsBipartite :=
  ParentSystem.graph_isBipartite (pairParentSystem baseSize depth)

theorem pairGraph_isTwoDegenerate (baseSize depth : ℕ) :
    IsTwoDegenerate (pairParentSystem baseSize depth).graph :=
  ParentSystem.graph_isTwoDegenerate (pairParentSystem baseSize depth)

theorem pairGraphOverFin_isBipartite (baseSize depth : ℕ) :
    (pairGraphOverFin baseSize depth).IsBipartite :=
  isBipartite_of_iso (pairGraphOverFinIso baseSize depth)
    (pairGraph_isBipartite baseSize depth)

theorem pairGraphOverFin_isTwoDegenerate (baseSize depth : ℕ) :
    IsTwoDegenerate (pairGraphOverFin baseSize depth) :=
  isTwoDegenerate_of_iso (pairGraphOverFinIso baseSize depth)
    (pairGraph_isTwoDegenerate baseSize depth)

open Classical in
theorem degree_gt_two_of_three_neighbors
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (v x y z : V)
    (hx : G.Adj v x) (hy : G.Adj v y) (hz : G.Adj v z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    2 < G.degree v := by
  classical
  change 2 < (G.neighborFinset v).card
  apply Finset.two_lt_card_iff.mpr
  exact ⟨x, y, z,
    (G.mem_neighborFinset v x).mpr hx,
    (G.mem_neighborFinset v y).mpr hy,
    (G.mem_neighborFinset v z).mpr hz,
    hxy, hxz, hyz⟩

open Classical in
theorem pairGraph_exists_adj_degree_gt_two
    (baseSize depth : ℕ) (hbase : 4 ≤ baseSize) (hdepth : 2 ≤ depth) :
    ∃ u v : PairVertex baseSize depth,
      (pairParentSystem baseSize depth).graph.Adj u v ∧
      2 < (pairParentSystem baseSize depth).graph.degree u ∧
      2 < (pairParentSystem baseSize depth).graph.degree v := by
  classical
  let a : PairLayer baseSize 0 := ⟨0, by omega⟩
  let b : PairLayer baseSize 0 := ⟨1, by omega⟩
  let c : PairLayer baseSize 0 := ⟨2, by omega⟩
  let d : PairLayer baseSize 0 := ⟨3, by omega⟩
  letI pairDecidableEq : DecidableEq (PairLayer baseSize 0) := Classical.decEq _
  have hab : a ≠ b := by
    intro heq
    have hval := congrArg Fin.val heq
    change 0 = 1 at hval
    omega
  have hac : a ≠ c := by
    intro heq
    have hval := congrArg Fin.val heq
    change 0 = 2 at hval
    omega
  have had : a ≠ d := by
    intro heq
    have hval := congrArg Fin.val heq
    change 0 = 3 at hval
    omega
  have hbc : b ≠ c := by
    intro heq
    have hval := congrArg Fin.val heq
    change 1 = 2 at hval
    omega
  have hbd : b ≠ d := by
    intro heq
    have hval := congrArg Fin.val heq
    change 1 = 3 at hval
    omega
  have hcd : c ≠ d := by
    intro heq
    have hval := congrArg Fin.val heq
    change 2 = 3 at hval
    omega
  let ab : PairLayer baseSize 1 :=
    ⟨{a, b}, Finset.card_pair hab⟩
  let ac : PairLayer baseSize 1 :=
    ⟨{a, c}, Finset.card_pair hac⟩
  let ad : PairLayer baseSize 1 :=
    ⟨{a, d}, Finset.card_pair had⟩
  have habac : ab ≠ ac := by
    intro heq
    have hmem : b ∈ ab.val := by
      change b ∈ ({a, b} : Finset (PairLayer baseSize 0))
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    rw [heq] at hmem
    change b ∈ ({a, c} : Finset (PairLayer baseSize 0)) at hmem
    rcases Finset.mem_insert.mp hmem with hba | hbc'
    · exact hab hba.symm
    · exact hbc (Finset.mem_singleton.mp hbc')
  have habad : ab ≠ ad := by
    intro heq
    have hmem : b ∈ ab.val := by
      change b ∈ ({a, b} : Finset (PairLayer baseSize 0))
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    rw [heq] at hmem
    change b ∈ ({a, d} : Finset (PairLayer baseSize 0)) at hmem
    rcases Finset.mem_insert.mp hmem with hba | hbd'
    · exact hab hba.symm
    · exact hbd (Finset.mem_singleton.mp hbd')
  have hacad : ac ≠ ad := by
    intro heq
    have hmem : c ∈ ac.val := by
      change c ∈ ({a, c} : Finset (PairLayer baseSize 0))
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self c)
    rw [heq] at hmem
    change c ∈ ({a, d} : Finset (PairLayer baseSize 0)) at hmem
    rcases Finset.mem_insert.mp hmem with hca | hcd'
    · exact hac hca.symm
    · exact hcd (Finset.mem_singleton.mp hcd')
  let abc : PairLayer baseSize 2 :=
    ⟨{ab, ac}, Finset.card_pair habac⟩
  let va : PairVertex baseSize depth :=
    pairLayerEmbedding baseSize depth 0 (by omega) a
  let vb : PairVertex baseSize depth :=
    pairLayerEmbedding baseSize depth 0 (by omega) b
  let vab : PairVertex baseSize depth :=
    pairLayerEmbedding baseSize depth 1 (by omega) ab
  let vac : PairVertex baseSize depth :=
    pairLayerEmbedding baseSize depth 1 (by omega) ac
  let vad : PairVertex baseSize depth :=
    pairLayerEmbedding baseSize depth 1 (by omega) ad
  let vabc : PairVertex baseSize depth :=
    pairLayerEmbedding baseSize depth 2 (by omega) abc
  let G : SimpleGraph (PairVertex baseSize depth) :=
    (pairParentSystem baseSize depth).graph
  have ha_mem_ab : a ∈ ab.val := by
    change a ∈ ({a, b} : Finset (PairLayer baseSize 0))
    exact Finset.mem_insert_self a {b}
  have hb_mem_ab : b ∈ ab.val := by
    change b ∈ ({a, b} : Finset (PairLayer baseSize 0))
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  have ha_mem_ac : a ∈ ac.val := by
    change a ∈ ({a, c} : Finset (PairLayer baseSize 0))
    exact Finset.mem_insert_self a {c}
  have ha_mem_ad : a ∈ ad.val := by
    change a ∈ ({a, d} : Finset (PairLayer baseSize 0))
    exact Finset.mem_insert_self a {d}
  have hab_a : G.Adj vab va := by
    simpa only [G, vab, va] using
      pairGraph_parent_child_adj baseSize depth 0
        (by omega) ab a ha_mem_ab
  have hab_b : G.Adj vab vb := by
    simpa only [G, vab, vb] using
      pairGraph_parent_child_adj baseSize depth 0
        (by omega) ab b hb_mem_ab
  have hac_a : G.Adj vac va := by
    simpa only [G, vac, va] using
      pairGraph_parent_child_adj baseSize depth 0
        (by omega) ac a ha_mem_ac
  have had_a : G.Adj vad va := by
    simpa only [G, vad, va] using
      pairGraph_parent_child_adj baseSize depth 0
        (by omega) ad a ha_mem_ad
  have habc_ab : G.Adj vabc vab := by
    simpa only [G, vabc, vab] using
      pairGraph_parent_child_adj baseSize depth 1
        (by omega) abc ab (by
          change ab ∈ ({ab, ac} : Finset (PairLayer baseSize 1))
          exact Finset.mem_insert_self ab {ac})
  have hab_vac : vab ≠ vac := by
    intro heq
    apply habac
    exact (pairLayerEmbedding baseSize depth 1 (by omega)).inj' heq
  have hab_vad : vab ≠ vad := by
    intro heq
    apply habad
    exact (pairLayerEmbedding baseSize depth 1 (by omega)).inj' heq
  have hac_vad : vac ≠ vad := by
    intro heq
    apply hacad
    exact (pairLayerEmbedding baseSize depth 1 (by omega)).inj' heq
  have ha_b : va ≠ vb := by
    intro heq
    have hfin := (pairLayerEmbedding baseSize depth 0 (by omega)).inj' heq
    have hval := congrArg Fin.val hfin
    simp [a, b] at hval
  have ha_abc : va ≠ vabc := by
    intro heq
    have hlevel := congrArg
      (fun vertex : PairVertex baseSize depth => vertex.1.val) heq
    change 0 = 2 at hlevel
    omega
  have hb_abc : vb ≠ vabc := by
    intro heq
    have hlevel := congrArg
      (fun vertex : PairVertex baseSize depth => vertex.1.val) heq
    change 0 = 2 at hlevel
    omega
  have ha_degree : 2 < G.degree va :=
    degree_gt_two_of_three_neighbors G va vab vac vad
      hab_a.symm hac_a.symm had_a.symm
      hab_vac hab_vad hac_vad
  have hab_degree : 2 < G.degree vab :=
    degree_gt_two_of_three_neighbors G vab va vb vabc
      hab_a hab_b habc_ab.symm ha_b ha_abc hb_abc
  exact ⟨va, vab, hab_a.symm, ha_degree, hab_degree⟩

open Classical in
theorem pairGraphOverFin_exists_adj_degree_gt_two
    (baseSize depth : ℕ) (hbase : 4 ≤ baseSize) (hdepth : 2 ≤ depth) :
    ∃ u v : Fin (Fintype.card (PairVertex baseSize depth)),
      (pairGraphOverFin baseSize depth).Adj u v ∧
      2 < (pairGraphOverFin baseSize depth).degree u ∧
      2 < (pairGraphOverFin baseSize depth).degree v := by
  classical
  obtain ⟨u, v, hadj, hu, hv⟩ :=
    pairGraph_exists_adj_degree_gt_two baseSize depth hbase hdepth
  let e := pairGraphOverFinIso baseSize depth
  refine ⟨e u, e v, (e.map_rel_iff).mpr hadj, ?_, ?_⟩
  · simpa only [e.degree_eq] using hu
  · simpa only [e.degree_eq] using hv

open Classical in
theorem bipartition_maximum_degree_gt_two_of_adj
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) {u v : V}
    (hadj : G.Adj u v)
    (hu : 2 < G.degree u) (hv : 2 < G.degree v) :
    ∀ coloring : G.Coloring (Fin 2), ∀ side : Fin 2,
      2 < (Finset.univ.filter
        (fun vertex : V => coloring vertex = side)).sup
        (fun vertex => G.degree vertex) := by
  classical
  intro coloring side
  have hwitness :
      ∃ vertex : V,
        coloring vertex = side ∧ 2 < G.degree vertex := by
    by_cases hcolor : coloring u = side
    · exact ⟨u, hcolor, hu⟩
    · refine ⟨v, ?_, hv⟩
      have hproper : coloring u ≠ coloring v := coloring.valid hadj
      apply Fin.ext
      have hu_lt := (coloring u).isLt
      have hv_lt := (coloring v).isLt
      have hside_lt := side.isLt
      omega
  obtain ⟨vertex, hcolor, hdegree⟩ := hwitness
  have hmember :
      vertex ∈ Finset.univ.filter
        (fun candidate : V => coloring candidate = side) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ vertex, hcolor⟩
  exact lt_of_lt_of_le hdegree
    (Finset.le_sup (f := fun candidate => G.degree candidate) hmember)

open Classical in
theorem pairGraphOverFin_bipartition_maximum_degree_gt_two
    (baseSize depth : ℕ) (hbase : 4 ≤ baseSize) (hdepth : 2 ≤ depth) :
    ∀ coloring : (pairGraphOverFin baseSize depth).Coloring (Fin 2),
      ∀ side : Fin 2,
        2 < (Finset.univ.filter
          (fun vertex : Fin (Fintype.card (PairVertex baseSize depth)) =>
            coloring vertex = side)).sup
          (fun vertex => (pairGraphOverFin baseSize depth).degree vertex) := by
  classical
  obtain ⟨u, v, hadj, hu, hv⟩ :=
    pairGraphOverFin_exists_adj_degree_gt_two baseSize depth hbase hdepth
  exact bipartition_maximum_degree_gt_two_of_adj
    (pairGraphOverFin baseSize depth) hadj hu hv

theorem manuscriptVertexCount_tendsto_atTop :
    Filter.Tendsto manuscriptVertexCount Filter.atTop Filter.atTop := by
  have hscaled :
      Filter.Tendsto
        (fun dimension : ℕ =>
          3 * (hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ)))
        Filter.atTop Filter.atTop :=
    hammingRetentionProbability_mul_wordCount_tendsto_atTop.const_mul_atTop
      (by norm_num)
  have hceiling := tendsto_nat_ceil_atTop.comp hscaled
  apply hceiling.congr'
  filter_upwards [] with dimension
  change
    ⌈3 * (hammingRetentionProbability dimension *
      ((2 ^ dimension : ℕ) : ℝ))⌉₊ =
      manuscriptVertexCount dimension
  unfold manuscriptVertexCount
  congr 1
  ring

theorem manuscriptVertexCount_succ_le_two_mul
    (dimension : ℕ) :
    manuscriptVertexCount (dimension + 1) ≤
      2 * manuscriptVertexCount dimension := by
  have hfactor :
      Real.exp ((1 - midpointBeta) * Real.log 2) ≤ (2 : ℝ) := by
    calc
      Real.exp ((1 - midpointBeta) * Real.log 2) ≤
          Real.exp (Real.log 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_pos midpointBeta_pos log_two_pos]
      _ = 2 := Real.exp_log (by norm_num)
  have hrecurrence :
      hammingRetentionProbability (dimension + 1) *
          ((2 ^ (dimension + 1) : ℕ) : ℝ) =
        Real.exp ((1 - midpointBeta) * Real.log 2) *
          (hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ)) := by
    rw [hammingRetentionProbability_mul_wordCount_eq_exp,
      hammingRetentionProbability_mul_wordCount_eq_exp,
      ← Real.exp_add]
    congr 1
    push_cast
    ring
  unfold manuscriptVertexCount
  apply Nat.ceil_le.mpr
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    3 * hammingRetentionProbability (dimension + 1) *
        ((2 ^ (dimension + 1) : ℕ) : ℝ) =
      Real.exp ((1 - midpointBeta) * Real.log 2) *
        (3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
        rw [show
          3 * hammingRetentionProbability (dimension + 1) *
              ((2 ^ (dimension + 1) : ℕ) : ℝ) =
            3 * (hammingRetentionProbability (dimension + 1) *
              ((2 ^ (dimension + 1) : ℕ) : ℝ)) by ring,
          hrecurrence]
        ring
    _ ≤ 2 * (3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hfactor (by
          positivity [hammingRetentionProbability_pos dimension])
    _ ≤ 2 *
          (⌈3 * hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ)⌉₊ : ℝ) := by
        gcongr
        exact Nat.le_ceil _

theorem exists_manuscriptVertexCount_bracket
    (minimum n : ℕ)
    (hminimum : manuscriptVertexCount minimum ≤ n) :
    ∃ dimension : ℕ,
      minimum ≤ dimension ∧
      manuscriptVertexCount dimension ≤ n ∧
      n < manuscriptVertexCount (dimension + 1) := by
  have hlarge :
      ∀ᶠ dimension : ℕ in Filter.atTop,
        n < manuscriptVertexCount dimension := by
    have hevent := Filter.tendsto_atTop.1
      manuscriptVertexCount_tendsto_atTop (n + 1)
    filter_upwards [hevent] with dimension hdimension
    omega
  obtain ⟨dimension, hdimension, hafter⟩ :=
    (hlarge.and (Filter.eventually_ge_atTop minimum)).exists
  have hexists :
      ∃ offset : ℕ,
        n < manuscriptVertexCount (minimum + offset) := by
    refine ⟨dimension - minimum, ?_⟩
    rw [Nat.add_sub_of_le hafter]
    exact hdimension
  let offset : ℕ := Nat.find hexists
  have hnext :
      n < manuscriptVertexCount (minimum + offset) :=
    Nat.find_spec hexists
  have hoffset : 0 < offset := by
    by_contra hnot
    have hzero : offset = 0 := Nat.eq_zero_of_not_pos hnot
    simp [hzero] at hnext
    omega
  refine ⟨minimum + (offset - 1), by omega, ?_, ?_⟩
  · have hbefore :
        ¬ n < manuscriptVertexCount (minimum + (offset - 1)) := by
      exact Nat.find_min hexists (by omega)
    exact Nat.le_of_not_gt hbefore
  · rw [show minimum + (offset - 1) + 1 = minimum + offset by omega]
    exact hnext

end

end Erdos146

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

open Classical in
theorem solution :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧
      H.IsBipartite ∧
      IsTwoDegenerate H ∧
      (∀ coloring : H.Coloring (Fin 2), ∀ side : Fin 2,
        2 < (Finset.univ.filter
          (fun vertex : Fin q => coloring vertex = side)).sup
          (fun vertex => H.degree vertex)) ∧
      ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((3 : ℝ) / 2 + ε) ≤
            (SimpleGraph.extremalNumber n H : ℝ) := by
  classical
  obtain ⟨baseSize, depth, hbase, hdepth,
    hdepth_window, hsubsequence⟩ :=
    eventually_manuscriptVertexCount_power_le_extremalNumber
  have hwidth : certifiedWindowWidth < 1 := by
    rw [← entropyWindow_eq_certifiedWindowWidth]
    linarith [entropyLowerEndpoint_pos, entropyUpperEndpoint_lt_one]
  have hproduct :
      0 ≤ (depth : ℝ) * (1 - certifiedWindowWidth) :=
    mul_nonneg (Nat.cast_nonneg depth) (sub_nonneg.mpr hwidth.le)
  have hdepth_real : (2 : ℝ) < (depth : ℝ) := by
    nlinarith
  have hdepth_nat : 2 < depth := by
    exact_mod_cast hdepth_real
  have hdepth_two : 2 ≤ depth := by
    omega
  let forbidden :
      SimpleGraph (Fin (Fintype.card (PairVertex baseSize depth))) :=
    pairGraphOverFin baseSize depth
  have hnoisolated :
      ∀ vertex : Fin (Fintype.card (PairVertex baseSize depth)),
        ∃ neighbor, forbidden.Adj vertex neighbor := by
    exact pairGraphOverFin_forall_exists_adj
      baseSize depth hbase hdepth
  refine ⟨Fintype.card (PairVertex baseSize depth), forbidden,
    pairGraphOverFin_connected baseSize depth (by omega) hdepth,
    pairGraphOverFin_isBipartite baseSize depth,
    pairGraphOverFin_isTwoDegenerate baseSize depth,
    ?_,
    1 / (2 : ℝ) ^ manuscriptExtremalPower,
    exponentGain, ?_, exponentGain_pos, ?_⟩
  · simpa only [forbidden] using
      pairGraphOverFin_bipartition_maximum_degree_gt_two
        baseSize depth hbase hdepth_two
  · exact one_div_pos.mpr
      (Real.rpow_pos_of_pos (by norm_num) manuscriptExtremalPower)
  · obtain ⟨minimum, hminimum⟩ :=
      Filter.eventually_atTop.1 hsubsequence
    apply Filter.eventually_atTop.2
    refine ⟨manuscriptVertexCount minimum, ?_⟩
    intro n hn
    obtain ⟨dimension, hdimension, hbelow, habove⟩ :=
      exists_manuscriptVertexCount_bracket minimum n hn
    have hdouble :=
      manuscriptVertexCount_succ_le_two_mul dimension
    have hn_bound :
        n ≤ 2 * manuscriptVertexCount dimension := by
      omega
    have hn_real :
        (n : ℝ) ≤
          2 * (manuscriptVertexCount dimension : ℝ) := by
      exact_mod_cast hn_bound
    have hsubseq := hminimum dimension hdimension
    have hmonotone :
        SimpleGraph.extremalNumber
            (manuscriptVertexCount dimension) forbidden ≤
          SimpleGraph.extremalNumber n forbidden :=
      CompactnessConjecture.extremalNumber_monotone_of_no_isolated
        forbidden hnoisolated hbelow
    change
      (1 / (2 : ℝ) ^ manuscriptExtremalPower) *
          (n : ℝ) ^ manuscriptExtremalPower ≤
        (SimpleGraph.extremalNumber n forbidden : ℝ)
    calc
      (1 / (2 : ℝ) ^ manuscriptExtremalPower) *
          (n : ℝ) ^ manuscriptExtremalPower ≤
        (1 / (2 : ℝ) ^ manuscriptExtremalPower) *
          (2 * (manuscriptVertexCount dimension : ℝ)) ^
            manuscriptExtremalPower := by
          apply mul_le_mul_of_nonneg_left
          · exact Real.rpow_le_rpow
              (Nat.cast_nonneg n) hn_real
              manuscriptExtremalPower_pos.le
          · positivity
      _ = (manuscriptVertexCount dimension : ℝ) ^
            manuscriptExtremalPower := by
          rw [Real.mul_rpow (by norm_num)
            (Nat.cast_nonneg (manuscriptVertexCount dimension))]
          have htwo :
              (2 : ℝ) ^ manuscriptExtremalPower ≠ 0 :=
            (Real.rpow_pos_of_pos (by norm_num)
              manuscriptExtremalPower).ne'
          field_simp [htwo]
      _ ≤ (SimpleGraph.extremalNumber
            (manuscriptVertexCount dimension) forbidden : ℝ) :=
          hsubseq
      _ ≤ (SimpleGraph.extremalNumber n forbidden : ℝ) := by
          exact_mod_cast hmonotone
