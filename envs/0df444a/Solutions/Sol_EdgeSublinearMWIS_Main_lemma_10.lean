-- Prove2me | solution 1 for EdgeSublinearMWIS.Main.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T17:27:12.760441+00:00
-- url     : https://prove2.me/submissions/8962eb84-5ac7-4bf7-ae98-876acecb641c

import Definitions.Def_EdgeSublinearMWIS_Main_Graphs
import Theorems.Thm_AKSSorting_Core_expander_exists
import Theorems.Thm_EdgeSublinearMWIS_Main_treewidth_separator
import Definitions.Def_EdgeSublinearMWIS_Main_Paths
import Theorems.Thm_EdgeSublinearMWIS_Main_lemma_9

noncomputable section

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
end

noncomputable section

open scoped Classical
open EdgeSublinearMWIS.Main TreewidthApprox.Pushed
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.ExpanderSeparator

 theorem partition_card {V : Type} [DecidableEq V] (W L S R : Finset V) (hp : IsPartition3 W L S R) :
    L.card+S.card+R.card=W.card := by
  have hLSR : Disjoint (L∪S) R := Finset.disjoint_union_left.mpr ⟨hp.2.1,hp.2.2.1⟩
  rw [←hp.2.2.2,Finset.card_union_of_disjoint hLSR,Finset.card_union_of_disjoint hp.1]

 theorem partition_card_inter {V : Type} [Fintype V] [DecidableEq V]
    (L S R A : Finset V) (hp : IsPartition3 Finset.univ L S R) :
    (L∩A).card+(S∩A).card+(R∩A).card=A.card := by
  apply partition_card A (L∩A) (S∩A) (R∩A)
  refine ⟨hp.1.mono Finset.inter_subset_left Finset.inter_subset_left,
    hp.2.1.mono Finset.inter_subset_left Finset.inter_subset_left,
    hp.2.2.1.mono Finset.inter_subset_left Finset.inter_subset_left,?_⟩
  rw [←Finset.union_inter_distrib_right,←Finset.union_inter_distrib_right,hp.2.2.2,Finset.univ_inter]

 theorem bipartition_card {V : Type} [Fintype V] [DecidableEq V]
    (A B X : Finset V) (hAB : Disjoint A B) (hu : A∪B=Finset.univ) :
    (X∩A).card+(X∩B).card=X.card := by
  have hd : Disjoint (X∩A) (X∩B) := hAB.mono Finset.inter_subset_right Finset.inter_subset_right
  rw [←Finset.card_union_of_disjoint hd,←Finset.inter_union_distrib_left,hu,Finset.inter_univ]

 theorem swap {V : Type} (G : SimpleGraph V) (A B : Finset V) (k : ℕ) (ε : ℝ)
    (he : AKSSorting.Core.IsExpander G A B k ε) : AKSSorting.Core.IsExpander G B A k ε := by
  refine ⟨he.1.symm,?_,he.2.2.1,he.2.2.2.2,he.2.2.2.1⟩
  intro u v huv
  exact (he.2.1 u v huv).symm

 theorem far_side_small {n : ℕ} (G : SimpleGraph (Fin n)) (A B X R : Finset (Fin n)) (k : ℕ)
    (he : AKSSorting.Core.IsExpander G A B k (1/100))
    (hX : X⊆A) (hB : 0 < B.card) (hlarge : B.card  ≤  100*X.card) (hno : NoEdge G X R) :
    100*(R∩B).card  <  B.card := by
  have hxne : X.Nonempty := Finset.card_pos.mp (by omega)
  have hnsub : AKSSorting.Core.neighbours G X ⊆ (↑(B\R) : Set (Fin n)) := by
    intro v hv
    obtain ⟨x,hx,hxv⟩ := hv
    have hxA := hX hx
    have hxnotB : x∉B := fun hxB => Finset.disjoint_left.mp he.1 hxA hxB
    have hvB : v∈B := by
      rcases he.2.1 x v hxv with hh | hh
      · exact hh.2
      · exact False.elim (hxnotB hh.1)
    exact Finset.mem_sdiff.mpr ⟨hvB,fun hvR => hno x hx v hvR hxv⟩
  have hncard := Set.ncard_le_ncard hnsub
  simp only [Set.ncard_coe_finset] at hncard
  have hlR : (1/100:ℝ)*B.card  ≤  (X.card:ℝ) := by
    have hh : (B.card:ℝ)  ≤  100*(X.card:ℝ) := by exact_mod_cast hlarge
    linarith
  have hex := he.2.2.2.1 X hX hxne
  rw [min_eq_right hlR] at hex
  have hsum := Finset.card_sdiff_add_card_inter B R
  have hnR : ((AKSSorting.Core.neighbours G X).ncard:ℝ)  ≤  ((B\R).card:ℝ) := by exact_mod_cast hncard
  have hsR : ((B\R).card:ℝ)+((R∩B).card:ℝ)=(B.card:ℝ) := by exact_mod_cast (by simpa only [Finset.inter_comm] using hsum)
  have hfinal : 100*((R∩B).card:ℝ) < (B.card:ℝ) := by norm_num at hex; nlinarith
  exact_mod_cast hfinal

 theorem cut_contradiction {n : ℕ} (G : SimpleGraph (Fin n)) (A B L S R : Finset (Fin n)) (k m : ℕ)
    (he : AKSSorting.Core.IsExpander G A B k (1/100)) (hu : A∪B=Finset.univ)
    (hA : A.card=m) (hB : B.card=m) (hm : 0 < m)
    (hp : IsPartition3 Finset.univ L S R) (hno : NoEdge G L R)
    (hS : 100*S.card  ≤  m) (hR : m  ≤  2*R.card) (hLA : m  ≤  100*(L∩A).card) : False := by
  have hRB := far_side_small G A B (L∩A) R k he Finset.inter_subset_right (by omega) (by omega)
    (by intro x hx y hy; exact hno x (Finset.mem_inter.mp hx).1 y hy)
  have hRAcard := bipartition_card A B R he.1 hu
  have hRA : m  ≤  100*(R∩A).card := by omega
  have hLB := far_side_small G A B (R∩A) L k he Finset.inter_subset_right (by omega) (by omega)
    (by intro x hx y hy hxy; exact hno y hy x (Finset.mem_inter.mp hx).1 hxy.symm)
  have hBsum := partition_card_inter L S R B hp
  have hSB := Finset.card_le_card (Finset.inter_subset_left (s₁ := S) (s₂ := B))
  omega

 theorem separator_large {n : ℕ} (G : SimpleGraph (Fin n)) (A B S : Finset (Fin n)) (k m : ℕ)
    (he : AKSSorting.Core.IsExpander G A B k (1/100)) (hu : A∪B=Finset.univ)
    (hA : A.card=m) (hB : B.card=m) (hm : 0 < m) (hb : Balanced G Finset.univ S) :
    m  <  100*S.card := by
  by_contra hn
  have hS : 100*S.card  ≤  m := by omega
  obtain ⟨L,R,hp,hno,hL,hR⟩ := GraphHelpers.balanced_split G Finset.univ S hb
  have hncard : n=2*m := by
    have hh := Finset.card_union_of_disjoint he.1
    rw [hu,hA,hB,Finset.card_univ,Fintype.card_fin] at hh
    omega
  have hsum := partition_card Finset.univ L S R hp
  simp only [Finset.card_univ,Fintype.card_fin] at hsum hL hR
  have hLL : m  ≤  2*L.card := by omega
  have hRR : m  ≤  2*R.card := by omega
  by_cases hLA : m  ≤  100*(L∩A).card
  · exact cut_contradiction G A B L S R k m he hu hA hB hm hp hno hS hRR hLA
  · have hLAcard := bipartition_card A B L he.1 hu
    have hLB : m  ≤  100*(L∩B).card := by omega
    exact cut_contradiction G B A L S R k m (swap G A B k _ he)
      (by simpa only [Finset.union_comm] using hu) hB hA hm hp hno hS hRR hLB

end EdgeSublinearMWIS.Main.ExpanderSeparator
end

noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.ExpanderSeparator

 def sideA (m : ℕ) : Finset (Fin (m+m)) := (Finset.univ : Finset (Fin m)).map (Fin.castAddEmb m)
 def sideB (m : ℕ) : Finset (Fin (m+m)) := (Finset.univ : Finset (Fin m)).map (Fin.natAddEmb m)

 theorem sides_card (m : ℕ) : (sideA m).card=m ∧ (sideB m).card=m := by simp [sideA,sideB]

 theorem sides_disjoint (m : ℕ) : Disjoint (sideA m) (sideB m) := by
  apply Finset.disjoint_left.mpr
  intro v hA hB
  obtain ⟨u,hu,he⟩ := Finset.mem_map.mp hA
  obtain ⟨w,hw,hf⟩ := Finset.mem_map.mp hB
  have hv := congrArg (fun z : Fin (m+m) => z.val) (he.trans hf.symm)
  change u.val=m+w.val at hv
  have hh := u.isLt
  omega

 theorem sides_union (m : ℕ) : sideA m ∪ sideB m=Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro v
  by_cases hv : v.val < m
  · apply Finset.mem_union_left
    exact Finset.mem_map.mpr ⟨⟨v.val,hv⟩,Finset.mem_univ _,Fin.ext rfl⟩
  · apply Finset.mem_union_right
    apply Finset.mem_map.mpr
    refine ⟨⟨v.val-m,by have := v.isLt; omega⟩,Finset.mem_univ _,?_⟩
    apply Fin.ext
    change m+(v.val-m)=v.val
    omega

 theorem noisolated_left {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) (k : ℕ)
    (he : AKSSorting.Core.IsExpander G A B k (1/100)) (v : Fin n) (hv : v∈A) : ∃ u,G.Adj v u := by
  by_contra hn
  push_neg at hn
  have hh := he.2.2.2.1 {v} (by simpa using hv) (Finset.singleton_nonempty v)
  have hempty : AKSSorting.Core.neighbours G {v}=∅ := by
    ext u
    simp [AKSSorting.Core.neighbours,hn]
  rw [hempty,Set.ncard_empty,Nat.cast_zero] at hh
  have hp : 0 ≤ (1-(1/100:ℝ))*(1/(1/100:ℝ))*min (({v} : Finset (Fin n)).card:ℝ) ((1/100:ℝ)*B.card) := by positivity
  linarith

 theorem bounded_degree_family : ∃ k : ℕ, 0 < k ∧ ∀ m : ℕ, 0 < m →
    ∃ H : SimpleGraph (Fin (m+m)), (∀ v,degree H v ≤ k) ∧ (∀ v,∃ u,H.Adj v u) ∧
      m ≤ 100*(PlantedSubgraphLD.tw H+1) := by
  obtain ⟨k,hk,hfam⟩ := AKSSorting.Core.expander_exists (1/100) 1 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨k,hk,?_⟩
  intro m hm
  have hcards := sides_card m
  obtain ⟨H,hH⟩ := hfam (Fin (m+m)) (sideA m) (sideB m) (sides_disjoint m)
    (by rw [hcards.1,hcards.2]; simp) (by rw [hcards.1,hcards.2]; simp)
  refine ⟨H,?_,?_,?_⟩
  · intro v
    exact (Set.encard_le_coe_iff_finite_ncard_le.mp (hH.2.2.1 v)).2
  · intro v
    have hv : v∈sideA m ∪ sideB m := by rw [sides_union]; exact Finset.mem_univ _
    rcases Finset.mem_union.mp hv with hv | hv
    · exact noisolated_left H _ _ k hH v hv
    · exact noisolated_left H _ _ k (swap H _ _ k _ hH) v hv
  · obtain ⟨S,hbal,hsize⟩ := treewidth_separator H Finset.univ
    have hl := separator_large H (sideA m) (sideB m) S k m hH (sides_union m) hcards.1 hcards.2 hm hbal
    omega

end EdgeSublinearMWIS.Main.ExpanderSeparator
end

noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.SubcubicGadget

variable {n k : ℕ} (H : SimpleGraph (Fin n)) (hd : ∀ v, degree H v ≤ k)

 def port (u v : Fin n) (h : H.Adj u v) : Fin k :=
  let e := Fintype.equivFin (H.neighborSet u)
  ⟨(e ⟨v,h⟩).val, (e ⟨v,h⟩).isLt.trans_le (by simpa only [Set.fintypeCard_eq_ncard,degree] using hd u)⟩

 theorem port_inj (u v w : Fin n) (hv : H.Adj u v) (hw : H.Adj u w)
    (he : port H hd u v hv=port H hd u w hw) : v=w := by
  have hh : Fintype.equivFin (H.neighborSet u) ⟨v,hv⟩ = Fintype.equivFin (H.neighborSet u) ⟨w,hw⟩ :=
    Fin.ext (by simpa only [port] using congrArg (fun z : Fin k => z.val) he)
  exact congrArg Subtype.val ((Fintype.equivFin (H.neighborSet u)).injective hh)

 def external (x y : Fin n × Fin k) : Prop :=
  ∃ h : H.Adj x.1 y.1, port H hd x.1 y.1 h=x.2 ∧ port H hd y.1 x.1 h.symm=y.2

 theorem external_symm {x y : Fin n × Fin k} (h : external H hd x y) : external H hd y x := by
  obtain ⟨h,hx,hy⟩ := h
  exact ⟨h.symm,hy,hx⟩

 theorem external_unique {x y z : Fin n × Fin k} (hy : external H hd x y) (hz : external H hd x z) : y=z := by
  obtain ⟨hy,hyx,hyy⟩ := hy
  obtain ⟨hz,hzx,hzz⟩ := hz
  have he := port_inj H hd x.1 y.1 z.1 hy hz (hyx.trans hzx.symm)
  apply Prod.ext he
  have hh : port H hd y.1 x.1 hy.symm=z.2 := by simpa only [←he] using hzz
  exact hyy.symm.trans hh

 def graph : SimpleGraph (Fin n × Fin k) where
  Adj x y := (x.1=y.1 ∧ (x.2.val+1=y.2.val ∨ y.2.val+1=x.2.val)) ∨ external H hd x y
  symm := ⟨by
    intro x y hh
    rcases hh with ⟨he,hr⟩ | hh
    · exact Or.inl ⟨he.symm,hr.symm⟩
    · exact Or.inr (external_symm H hd hh)⟩
  loopless := ⟨by
    intro x hh
    rcases hh with ⟨_,hr⟩ | ⟨h,_,_⟩
    · omega
    · exact H.irrefl h⟩

 def externalChoice (x : Fin n × Fin k) : Fin n × Fin k :=
  if he : ∃ y, external H hd x y then he.choose else x

 theorem external_eq_choice {x y : Fin n × Fin k} (hy : external H hd x y) : y=externalChoice H hd x := by
  unfold externalChoice
  rw [dif_pos ⟨y,hy⟩]
  exact external_unique H hd hy (Exists.choose_spec (show ∃ z,external H hd x z from ⟨y,hy⟩))

 def left (x : Fin n × Fin k) : Fin n × Fin k :=
  (x.1,⟨x.2.val-1,(Nat.sub_le _ _).trans_lt x.2.isLt⟩)

 def right (x : Fin n × Fin k) : Fin n × Fin k :=
  (x.1,if hh : x.2.val+1<k then ⟨x.2.val+1,hh⟩ else x.2)

 theorem neighbors_subset (x : Fin n × Fin k) :
    (graph H hd).neighborSet x ⊆ (↑({left x,right x,externalChoice H hd x} : Finset (Fin n × Fin k)) : Set _) := by
  intro y hy
  rcases hy with ⟨hbase,hstep⟩ | he
  · rcases hstep with hr | hl
    · have heq : y=right x := by
        have hf : y.1=(right x).1 := hbase.symm
        apply Prod.ext hf
        unfold right
        dsimp only
        rw [dif_pos (by rw [hr]; exact y.2.isLt)]
        exact Fin.ext hr.symm
      simp [heq]
    · have heq : y=left x := by
        have hf : y.1=(left x).1 := hbase.symm
        apply Prod.ext hf
        apply Fin.ext
        dsimp only [left]
        omega
      simp [heq]
  · simp [external_eq_choice H hd he]

 theorem degree_bound (x : Fin n × Fin k) : ((graph H hd).neighborSet x).ncard ≤ 3 := by
  have hh := Set.ncard_le_ncard (neighbors_subset H hd x)
  rw [Set.ncard_coe_finset] at hh
  have hc : ({left x,right x,externalChoice H hd x} : Finset (Fin n × Fin k)).card ≤ 3 := by
    have h1 := Finset.card_insert_le (left x) ({right x,externalChoice H hd x} : Finset (Fin n × Fin k))
    have h2 := Finset.card_insert_le (right x) ({externalChoice H hd x} : Finset (Fin n × Fin k))
    simp only [Finset.card_singleton] at h2
    omega
  exact hh.trans hc

 def numbered : SimpleGraph (Fin (n*k)) := (graph H hd).comap finProdFinEquiv.symm

end EdgeSublinearMWIS.Main.SubcubicGadget
end

noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.SubcubicGadget
variable {n k : ℕ} (H : SimpleGraph (Fin n)) (hd : ∀ v, degree H v ≤ k)

 def label {t : ℕ} (ht : n*k ≤ t) : (Fin n × Fin k) ↪ Fin t where
  toFun x := Fin.castLE ht (finProdFinEquiv x)
  inj' := by
    intro x y hh
    apply finProdFinEquiv.injective
    exact Fin.ext (congrArg (fun z : Fin t => z.val) hh)

 def padded {t : ℕ} (ht : n*k ≤ t) : SimpleGraph (Fin t) := (graph H hd).map (label ht)

 theorem padded_degree {t : ℕ} (ht : n*k ≤ t) (v : Fin t) : degree (padded H hd ht) v ≤ 3 := by
  by_cases hv : ∃ x, label ht x=v
  · obtain ⟨x,rfl⟩ := hv
    change ((((graph H hd).map (label ht)).neighborSet (label ht x)).ncard) ≤ 3
    rw [SimpleGraph.neighborSet_map]
    exact (Set.ncard_image_le (s := (graph H hd).neighborSet x) (f := label ht)).trans (degree_bound H hd x)
  · have he : (padded H hd ht).neighborSet v=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      obtain ⟨x,z,hxz,hx,hz⟩ := (SimpleGraph.map_adj (label ht) (graph H hd) v y).mp hy
      exact hv ⟨x,hx⟩
    change ((padded H hd ht).neighborSet v).ncard ≤ 3
    rw [he]; simp

 def fiberHom (u : Fin n) : SimpleGraph.pathGraph k →g graph H hd where
  toFun i := (u,i)
  map_rel' := by intro i j hij; exact Or.inl ⟨rfl,SimpleGraph.pathGraph_adj.mp hij⟩

 def fiberWalk (u : Fin n) (i j : Fin k) : (graph H hd).Walk (u,i) (u,j) :=
  ((SimpleGraph.pathGraph_preconnected k i j).some).map (fiberHom H hd u)

 theorem fiber_mem (u : Fin n) (i j : Fin k) (x : Fin n × Fin k) (hx : x ∈ (fiberWalk H hd u i j).support) : x.1=u := by
  dsimp only [fiberWalk,fiberHom] at hx
  rw [SimpleGraph.Walk.support_map] at hx
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hx
  rfl

 def edgeWalk (hk : 0 < k) (u v : Fin n) (h : H.Adj u v) :
    (graph H hd).Walk (u,⟨0,hk⟩) (v,⟨0,hk⟩) :=
  (fiberWalk H hd u ⟨0,hk⟩ (port H hd u v h)).append
    ((SimpleGraph.Adj.toWalk (Or.inr ⟨h,rfl,rfl⟩ : (graph H hd).Adj (u,port H hd u v h) (v,port H hd v u h.symm))).append
      (fiberWalk H hd v (port H hd v u h.symm) ⟨0,hk⟩))

 theorem edgeWalk_mem (hk : 0 < k) (u v : Fin n) (h : H.Adj u v) (x : Fin n × Fin k)
    (hx : x ∈ (edgeWalk H hd hk u v h).support) : x.1=u ∨ x.1=v := by
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hx with hx | hx
  · exact Or.inl (fiber_mem H hd _ _ _ _ hx)
  · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hx with hx | hx
    · change x ∈ [(u,port H hd u v h),(v,port H hd v u h.symm)] at hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exact Or.inr (fiber_mem H hd _ _ _ _ hx)

 def labelHom {t : ℕ} (ht : n*k ≤ t) : graph H hd →g padded H hd ht where
  toFun := label ht
  map_rel' := by intro x y hxy; exact SimpleGraph.map_adj_apply.mpr hxy

 def mappedWalk {t : ℕ} (ht : n*k ≤ t) (hk : 0 < k) (e : EdgeIndex H) :
    (padded H hd ht).Walk (label ht (e.val.1,⟨0,hk⟩)) (label ht (e.val.2,⟨0,hk⟩)) :=
  (edgeWalk H hd hk e.val.1 e.val.2 e.property.2).map (labelHom H hd ht)

 theorem mapped_mem {t : ℕ} (ht : n*k ≤ t) (hk : 0 < k) (e : EdgeIndex H) (z : Fin t)
    (hz : z ∈ (mappedWalk H hd ht hk e).bypass.support) :
    ∃ x : Fin n × Fin k, label ht x=z ∧ (x.1=e.val.1 ∨ x.1=e.val.2) := by
  have hh := (mappedWalk H hd ht hk e).support_bypass_subset_support hz
  dsimp only [mappedWalk,labelHom] at hh
  rw [SimpleGraph.Walk.support_map] at hh
  obtain ⟨x,hx,heq⟩ := List.mem_map.mp hh
  exact ⟨x,heq,edgeWalk_mem H hd hk _ _ _ x hx⟩

 def embedding {t : ℕ} (ht : n*k ≤ t) (hk : 0 < k) : AlmostEmbedding H (padded H hd ht) where
  vertex v := label ht (v,⟨0,hk⟩)
  path e := (mappedWalk H hd ht hk e).bypass.support
  valid e := by
    let p := (mappedWalk H hd ht hk e).bypass
    refine ⟨⟨p.support_ne_nil,(mappedWalk H hd ht hk e).bypass_isPath.support_nodup,?_,p.isChain_adj_support⟩,?_,?_⟩
    · intro v hv; exact Finset.mem_univ _
    · simpa only [p.head_support] using List.head?_eq_some_head p.support_ne_nil
    · simpa only [p.getLast_support] using List.getLast?_eq_some_getLast p.support_ne_nil
  disjoint e f h11 h12 h21 h22 z hze hzf := by
    obtain ⟨x,hx,hxe⟩ := mapped_mem H hd ht hk e z hze
    obtain ⟨y,hy,hyf⟩ := mapped_mem H hd ht hk f z hzf
    have hxy := (label ht).injective (hx.trans hy.symm)
    have hf : x.1=y.1 := congrArg Prod.fst hxy
    rcases hxe with hxe | hxe <;> rcases hyf with hyf | hyf <;> aesop

end EdgeSublinearMWIS.Main.SubcubicGadget
end

noncomputable section

open scoped Classical
open EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.ExpanderSeparator
open RobertsonSeymour1986.GM5
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.ExpanderSeparator

 theorem width_witness {n : ℕ} (G : SimpleGraph (Fin n)) : TreewidthLE G (PlantedSubgraphLD.tw G) := by
  have hne : {w : ℕ | TreewidthLE G w}.Nonempty := by
    refine ⟨n,PUnit,inferInstance,⊥,(fun _ => Finset.univ),?_,?_⟩
    · refine ⟨?_,?_,?_,?_⟩
      · exact ⟨SimpleGraph.Connected.of_subsingleton,by simp⟩
      · intro v; exact ⟨PUnit.unit,Finset.mem_univ _⟩
      · intro u v h; exact ⟨PUnit.unit,Finset.mem_univ _,Finset.mem_univ _⟩
      · intro s s' s'' p hp hm; exact Finset.subset_univ _
    · intro s; simp
  exact Nat.sInf_mem hne

 theorem width_transfer {n k t : ℕ} (H : SimpleGraph (Fin n)) (hd : ∀ v,degree H v ≤ k)
    (hi : ∀ v,∃ u,H.Adj v u) (hk : 0 < k) (ht : n*k ≤ t) :
    PlantedSubgraphLD.tw H ≤ 2*k*(PlantedSubgraphLD.tw (SubcubicGadget.padded H hd ht)+1) := by
  let G := SubcubicGadget.padded H hd ht
  obtain ⟨T,ft,tree,bags,hdec,hsize⟩ := width_witness G
  obtain ⟨new,hnew,hcard⟩ := lemma_9 H G k (PlantedSubgraphLD.tw G+1) hd hi
    (SubcubicGadget.embedding H hd ht hk) T tree bags hdec hsize
  apply Nat.sInf_le
  exact ⟨T,ft,tree,new,hnew,fun z => (hcard z).trans (Nat.le_succ _)⟩

end EdgeSublinearMWIS.Main.ExpanderSeparator

theorem solution :
    ∃ (c : ℝ) (t₀ : ℕ), 0 < c ∧ ∀ t ≥ t₀,
      ∃ H : SimpleGraph (Fin t), (∀ v,degree H v ≤ 3) ∧
        c*t ≤ (PlantedSubgraphLD.tw H:ℝ) := by
  obtain ⟨k,hk,hfam⟩ := bounded_degree_family
  let C := 10000*(k+1)^2
  have hC : 0 < C := by dsimp [C]; positivity
  have hCR : 0 < (C:ℝ) := by exact_mod_cast hC
  refine ⟨1/(C:ℝ),C,by positivity,?_⟩
  intro t ht
  let m := t/(2*k)
  have hmod : t%(2*k) < 2*k := Nat.mod_lt _ (by omega)
  have hdiv : (2*k)*m+t%(2*k)=t := by simpa only [m] using Nat.div_add_mod t (2*k)
  have hm : 0 < m := by
    by_contra hn
    have hm0 : m=0 := Nat.eq_zero_of_not_pos hn
    rw [hm0,Nat.mul_zero] at hdiv
    dsimp only [C] at ht
    nlinarith
  obtain ⟨H,hd,hi,hwidth⟩ := hfam m hm
  have hsize : (m+m)*k ≤ t := by
    calc
      _ = (2*k)*m := by ring
      _ ≤ (2*k)*m+t%(2*k) := Nat.le_add_right _ _
      _ = t := hdiv
  let G := SubcubicGadget.padded H hd hsize
  have htrans := width_transfer H hd hi hk hsize
  have hmwidth : m ≤ 100*(2*k*(PlantedSubgraphLD.tw G+1)+1) :=
    hwidth.trans (Nat.mul_le_mul_left 100 (Nat.add_le_add_right htrans 1))
  have hmul := Nat.mul_le_mul_left (2*k) hmwidth
  have hpre : t ≤ 400*k^2*PlantedSubgraphLD.tw G+400*k^2+202*k := by nlinarith
  have hpos : 1 ≤ PlantedSubgraphLD.tw G := by
    by_contra hn
    have hw0 : PlantedSubgraphLD.tw G=0 := by omega
    rw [hw0,Nat.mul_zero] at hpre
    dsimp only [C] at ht
    nlinarith
  have hcoeff : 400*k^2+(400*k^2+202*k) ≤ C := by dsimp [C]; nlinarith
  have hprod := Nat.mul_le_mul_left (400*k^2+202*k) hpos
  have htw : t ≤ C*PlantedSubgraphLD.tw G := by
    have hmulC := Nat.mul_le_mul_right (PlantedSubgraphLD.tw G) hcoeff
    nlinarith
  refine ⟨G,SubcubicGadget.padded_degree H hd hsize,?_⟩
  have hreal : (t:ℝ) ≤ (PlantedSubgraphLD.tw G:ℝ)*(C:ℝ) := by
    exact_mod_cast (by simpa only [Nat.mul_comm] using htw)
  simpa only [div_eq_mul_inv,one_mul,mul_one,mul_comm] using (div_le_iff₀ hCR).mpr hreal
end
