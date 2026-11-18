-- Prove2me | solution 2 for EdgeSublinearMWIS.Main.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:40:44.653564+00:00
-- url     : https://prove2.me/submissions/ffd52f79-f5f0-4f7e-bdc9-cf6604f462d8

import Definitions.Def_EdgeSublinearMWIS_Main_Graphs
import Theorems.Thm_DvorakNorin2018_balanced_separators_treewidth
import Theorems.Thm_EdgeSublinearMWIS_Main_treewidth_separator


open scoped BigOperators
open EdgeSublinearMWIS.Main TreewidthApprox.Pushed
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.GraphHelpers

 theorem avoid_refl {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    {u : Fin n} (hu : u ∉ X) : AvoidReach G X u u := by
  exact ⟨.nil, by simpa using hu⟩

 theorem avoid_symm {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    {u v : Fin n} (h : AvoidReach G X u v) : AvoidReach G X v u := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, by simpa using hp⟩

 theorem avoid_trans {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    {u v w : Fin n} (h1 : AvoidReach G X u v) (h2 : AvoidReach G X v w) : AvoidReach G X u w := by
  obtain ⟨p1, h1⟩ := h1
  obtain ⟨p2, h2⟩ := h2
  refine ⟨p1.append p2, ?_⟩
  intro z hz
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hz with hz | hz
  · exact h1 z hz
  · exact h2 z hz

 theorem comp_mem {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) (u v : Fin n) :
    v ∈ avoidComp G X u ↔ AvoidReach G X u v := by
  classical
  simp [avoidComp]

 theorem comp_self {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    {u : Fin n} (hu : u ∉ X) : u ∈ avoidComp G X u :=
  (comp_mem G X u u).mpr (avoid_refl G X hu)

 theorem comp_outside {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    {u v : Fin n} (hv : v ∈ avoidComp G X u) : v ∉ X := by
  obtain ⟨p, hp⟩ := (comp_mem G X u v).mp hv
  exact hp v p.end_mem_support

 theorem comp_eq {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    {u v : Fin n} (hv : v ∈ avoidComp G X u) : avoidComp G X u = avoidComp G X v := by
  classical
  ext z
  simp only [comp_mem]
  have huv := (comp_mem G X u v).mp hv
  exact ⟨fun h => avoid_trans G X (avoid_symm G X huv) h, fun h => avoid_trans G X huv h⟩

 theorem comp_disjoint_or_eq {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (u v : Fin n) : Disjoint (avoidComp G X u) (avoidComp G X v) ∨
      avoidComp G X u = avoidComp G X v := by
  classical
  by_cases h : Disjoint (avoidComp G X u) (avoidComp G X v)
  · exact Or.inl h
  · obtain ⟨z, hzu, hzv⟩ := Finset.not_disjoint_iff.mp h
    exact Or.inr ((comp_eq G X hzu).trans (comp_eq G X hzv).symm)

 theorem comp_adj {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    {u v w : Fin n} (hv : v ∈ avoidComp G X u) (ha : G.Adj v w) (hw : w ∉ X) :
    w ∈ avoidComp G X u := by
  apply (comp_mem G X u w).mpr
  refine avoid_trans G X ((comp_mem G X u v).mp hv) ⟨ha.toWalk, ?_⟩
  intro z hz
  have hvX := comp_outside G X hv
  simp only [SimpleGraph.Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl
  · exact hvX
  · exact hw

 theorem component_subset {n : ℕ} (G : SimpleGraph (Fin n)) (W S : Finset (Fin n))
    {D : Finset (Fin n)} (hD : D ∈ components G W S) : D ⊆ W \ S := by
  classical
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hD
  intro u hu
  have hx := comp_outside G (S ∪ (Finset.univ \ W)) hu
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, not_or,
    not_not] at hx
  exact Finset.mem_sdiff.mpr ⟨hx.2, hx.1⟩

 theorem component_cover {n : ℕ} (G : SimpleGraph (Fin n)) (W S : Finset (Fin n))
    {v : Fin n} (hv : v ∈ W \ S) :
    ∃ D ∈ components G W S, v ∈ D := by
  classical
  refine ⟨avoidComp G (S ∪ (Finset.univ \ W)) v, Finset.mem_image.mpr ⟨v, hv, rfl⟩, ?_⟩
  apply comp_self
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, not_or, not_not]
  exact ⟨(Finset.mem_sdiff.mp hv).2, (Finset.mem_sdiff.mp hv).1⟩

 theorem components_disjoint {n : ℕ} (G : SimpleGraph (Fin n)) (W S : Finset (Fin n))
    {D E : Finset (Fin n)} (hD : D ∈ components G W S) (hE : E ∈ components G W S) :
    Disjoint D E ∨ D = E := by
  classical
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hD
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hE
  exact comp_disjoint_or_eq G _ u v

 theorem component_noEdge {n : ℕ} (G : SimpleGraph (Fin n)) (W S : Finset (Fin n))
    {D : Finset (Fin n)} (hD : D ∈ components G W S) :
    NoEdge G D ((W \ S) \ D) := by
  classical
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hD
  intro v hv w hw ha
  have hwWS := (Finset.mem_sdiff.mp hw).1
  have hwX : w ∉ S ∪ (Finset.univ \ W) := by
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, not_or, not_not]
    exact ⟨(Finset.mem_sdiff.mp hwWS).2, (Finset.mem_sdiff.mp hwWS).1⟩
  exact (Finset.mem_sdiff.mp hw).2 (comp_adj G _ hv ha hwX)

 theorem balanced_split {n : ℕ} (G : SimpleGraph (Fin n)) (W S : Finset (Fin n))
    (hbalanced : Balanced G W S) : ∃ L R : Finset (Fin n),
      IsPartition3 W L S R ∧ NoEdge G L R ∧
        3 * L.card ≤ 2 * W.card ∧ 3 * R.card ≤ 2 * W.card := by
  classical
  let P := components G W S
  let unionOf : Finset (Finset (Fin n)) → Finset (Fin n) := fun A => A.biUnion id
  let candidates := P.powerset.filter (fun A => 3 * (unionOf A).card ≤ 2 * W.card)
  have hne : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, unionOf]
  obtain ⟨A, hA, hmax⟩ := candidates.exists_max_image (fun A => (unionOf A).card) hne
  have hAP : A ⊆ P := Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1
  have hcap : 3 * (unionOf A).card ≤ 2 * W.card := (Finset.mem_filter.mp hA).2
  let L := unionOf A
  let R := (W \ S) \ L
  have hL : L ⊆ W \ S := by
    intro v hv
    obtain ⟨D, hDA, hvD⟩ := Finset.mem_biUnion.mp hv
    exact component_subset G W S (hAP hDA) hvD
  have hDmax (D : Finset (Fin n)) (hDP : D ∈ P) : D.card ≤ L.card := by
    have hDcand : {D} ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.singleton_subset_iff.mpr hDP, ?_⟩
      simpa [unionOf] using hbalanced.2 D hDP
    simpa [unionOf] using hmax {D} hDcand
  have hRcap : 3 * R.card ≤ 2 * W.card := by
    by_contra hh
    have hsum : R.card + L.card ≤ W.card := by
      rw [show R.card + L.card = (W \ S).card from Finset.card_sdiff_add_card_eq_card hL]
      exact Finset.card_le_card Finset.sdiff_subset
    have hLsmall : 3 * L.card < W.card := by omega
    have hRne : R.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨v, hvR⟩ := hRne
    obtain ⟨D, hDP, hvD⟩ := component_cover G W S (Finset.mem_sdiff.mp hvR).1
    have hDdis : Disjoint L D := by
      apply (Finset.disjoint_biUnion_left A id D).mpr
      intro E hEA
      rcases components_disjoint G W S (hAP hEA) hDP with hdis | heq
      · exact hdis
      · have hvL : v ∈ L := Finset.mem_biUnion.mpr ⟨E, hEA, heq.symm ▸ hvD⟩
        exact False.elim ((Finset.mem_sdiff.mp hvR).2 hvL)
    have hDsmall := hDmax D hDP
    have hcard : (unionOf (insert D A)).card = D.card + L.card := by
      simp only [unionOf, Finset.biUnion_insert]
      exact Finset.card_union_of_disjoint hDdis.symm
    have hnew : insert D A ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.insert_subset hDP hAP, ?_⟩
      rw [hcard]
      omega
    have hmax' := hmax (insert D A) hnew
    rw [hcard] at hmax'
    have hDpos : 0 < D.card := Finset.card_pos.mpr ⟨v, hvD⟩
    change D.card + L.card ≤ L.card at hmax'
    omega
  have hNo : NoEdge G L R := by
    intro v hv u hu ha
    obtain ⟨D, hDA, hvD⟩ := Finset.mem_biUnion.mp hv
    have huD : u ∉ D := by
      intro huD
      exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_biUnion.mpr ⟨D, hDA, huD⟩)
    exact component_noEdge G W S (hAP hDA) v hvD u
      (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hu).1, huD⟩) ha
  refine ⟨L, R, ?_, hNo, hcap, hRcap⟩
  have hS := hbalanced.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hvL hvS
    exact (Finset.mem_sdiff.mp (hL hvL)).2 hvS
  · apply Finset.disjoint_left.mpr
    intro v hvL hvR
    exact (Finset.mem_sdiff.mp hvR).2 hvL
  · apply Finset.disjoint_left.mpr
    intro v hvS hvR
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hvR).1).2 hvS
  · ext v
    have hLv : v ∈ L → v ∈ W := fun h => (Finset.mem_sdiff.mp (hL h)).1
    have hSv : v ∈ S → v ∈ W := fun h => hS h
    simp only [Finset.mem_union, R, Finset.mem_sdiff]
    tauto

end EdgeSublinearMWIS.Main.GraphHelpers


open scoped BigOperators
open EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.GraphHelpers
open TreewidthApprox.Pushed RobertsonSeymour1986.GM5
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.TreewidthUpper

 theorem separationNumber_spec {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∀ W : Finset (Fin n), ∃ S, Balanced G W S ∧ S.card ≤ separationNumber G := by
  have hne : {s : ℕ | ∀ W : Finset (Fin n), ∃ S, Balanced G W S ∧ S.card ≤ s}.Nonempty := by
    refine ⟨n, ?_⟩
    intro W
    refine ⟨W, ⟨Finset.Subset.refl _, ?_⟩, ?_⟩
    · simp [components]
    · simpa using Finset.card_le_univ W
  exact Nat.sInf_mem hne

 theorem treewidth_le_separationNumber {n : ℕ} (G : SimpleGraph (Fin n)) :
    PlantedSubgraphLD.tw G ≤ 15 * separationNumber G := by
  have hsep : StableMSR.Recovery.Havens.HasBalancedSeparations G (separationNumber G) := by
    intro W
    obtain ⟨S, hbal, hsize⟩ := separationNumber_spec G W
    obtain ⟨L, R, hpart, hNo, hL, hR⟩ := balanced_split G W S hbal
    exact ⟨L, S, R, hpart, hNo, hsize, hL, hR⟩
  have htw := DvorakNorin2018.balanced_separators_treewidth G (separationNumber G) hsep
  exact Nat.sInf_le htw

end EdgeSublinearMWIS.Main.TreewidthUpper


open scoped BigOperators
open EdgeSublinearMWIS.Main
open EdgeSublinearMWIS.Main.TreewidthUpper
open RobertsonSeymour1986.GM5
set_option autoImplicit false

private theorem treewidth_witness {n : ℕ} (G : SimpleGraph (Fin n)) : TreewidthLE G (PlantedSubgraphLD.tw G) := by
  have hne : {w : ℕ | TreewidthLE G w}.Nonempty := by
    refine ⟨n, PUnit, inferInstance, ⊥, (fun _ => Finset.univ), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · exact ⟨SimpleGraph.Connected.of_subsingleton, by simp⟩
      · intro v; exact ⟨PUnit.unit, Finset.mem_univ _⟩
      · intro u v h; exact ⟨PUnit.unit, Finset.mem_univ _, Finset.mem_univ _⟩
      · intro s s' s'' p hp hm; exact Finset.subset_univ _
    · intro s; simp
  exact Nat.sInf_mem hne

private theorem separationNumber_le_treewidth_add_one {n : ℕ} (G : SimpleGraph (Fin n)) :
    separationNumber G ≤ PlantedSubgraphLD.tw G + 1 := by
  apply Nat.sInf_le
  intro W
  exact treewidth_separator G W

private theorem treewidth_pos_of_edge {n : ℕ} (G : SimpleGraph (Fin n))
    (hedge : 1 ≤ edgeCount G) : 1 ≤ PlantedSubgraphLD.tw G := by
  classical
  have hne : ((Finset.univ : Finset (Fin n × Fin n)).filter
    (fun e => e.1 < e.2 ∧ G.Adj e.1 e.2)).Nonempty :=
    Finset.card_pos.mp (by simpa [edgeCount] using hedge)
  obtain ⟨⟨u,v⟩, huv⟩ := hne
  have hadj := (Finset.mem_filter.mp huv).2.2
  obtain ⟨T, inst, tree, bags, dec, hsize⟩ := treewidth_witness G
  obtain ⟨t, hut, hvt⟩ := dec.2.2.1 u v hadj
  have htwo : 2 ≤ (bags t).card := Finset.one_lt_card.mpr ⟨u, hut, v, hvt, G.ne_of_adj hadj⟩
  have hs := hsize t
  omega

theorem solution :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      1 ≤ edgeCount G →
        c * separationNumber G ≤ (PlantedSubgraphLD.tw G : ℝ) ∧
          (PlantedSubgraphLD.tw G : ℝ) ≤ K * separationNumber G := by
  refine ⟨1 / 2, 15, by norm_num, by norm_num, ?_⟩
  intro n G hedge
  have hs : (separationNumber G : ℝ) ≤ (PlantedSubgraphLD.tw G : ℝ) + 1 := by
    exact_mod_cast separationNumber_le_treewidth_add_one G
  have hp : (1 : ℝ) ≤ PlantedSubgraphLD.tw G := by exact_mod_cast treewidth_pos_of_edge G hedge
  have hu : (PlantedSubgraphLD.tw G : ℝ) ≤ 15 * separationNumber G := by
    exact_mod_cast treewidth_le_separationNumber G
  constructor <;> nlinarith
