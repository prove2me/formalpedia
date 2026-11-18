-- Prove2me | solution 1 for EdgeSublinearMWIS.Main.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:33:40.986013+00:00
-- url     : https://prove2.me/submissions/eecba952-985e-4749-88e1-a6bc4d38283c

import Definitions.Def_EdgeSublinearMWIS_Main_Paths
import Definitions.Def_EdgeSublinearMWIS_Main_Graphs
import Theorems.Thm_DvorakNorin2018_balanced_separators_treewidth


open scoped BigOperators
open EdgeSublinearMWIS.Main
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.DecompositionHelpers

 theorem path_support_subset_walk {T : Type} (tree : SimpleGraph T) (acyclic : tree.IsAcyclic)
    {s t : T} (p : tree.Walk s t) (hp : p.IsPath) (q : tree.Walk s t) :
    p.support ⊆ q.support := by
  classical
  letI := acyclic.subsingleton_path s t
  have h : (⟨p, hp⟩ : tree.Path s t) = q.toPath := Subsingleton.elim _ _
  have he : p = q.toPath.val := congrArg Subtype.val h
  rw [he]
  exact q.support_toPath_subset_support

 theorem vertex_walk {n : ℕ} (G : SimpleGraph (Fin n)) {T : Type} (tree : SimpleGraph T)
    (bags : T → Finset (Fin n))
    (dec : RobertsonSeymour1986.GM5.IsTreeDecomposition G tree bags)
    {s t : T} {v : Fin n} (hs : v ∈ bags s) (ht : v ∈ bags t) :
    ∃ q : tree.Walk s t, ∀ z ∈ q.support, v ∈ bags z := by
  obtain ⟨q, hq⟩ := dec.1.connected.exists_isPath s t
  exact ⟨q, fun z hz => dec.2.2.2 s z t q hq hz (Finset.mem_inter.mpr ⟨hs, ht⟩)⟩

 theorem walk_bags {n : ℕ} (G : SimpleGraph (Fin n)) {T : Type} (tree : SimpleGraph T)
    (bags : T → Finset (Fin n))
    (dec : RobertsonSeymour1986.GM5.IsTreeDecomposition G tree bags)
    {u v : Fin n} (p : G.Walk u v) {s t : T} (hs : u ∈ bags s) (ht : v ∈ bags t) :
    ∃ q : tree.Walk s t, ∀ z ∈ q.support, ∃ x ∈ p.support, x ∈ bags z := by
  induction p generalizing s with
  | nil =>
    obtain ⟨q, hq⟩ := vertex_walk G tree bags dec hs ht
    exact ⟨q, fun z hz => ⟨_, by simp, hq z hz⟩⟩
  | @cons u v w hadj p ih =>
    obtain ⟨b, hu, hv⟩ := dec.2.2.1 u v hadj
    obtain ⟨q1, hq1⟩ := vertex_walk G tree bags dec hs hu
    obtain ⟨q2, hq2⟩ := ih hv ht
    refine ⟨q1.append q2, ?_⟩
    intro z hz
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hz with hz | hz
    · exact ⟨u, by simp, hq1 z hz⟩
    · obtain ⟨x, hx, hxz⟩ := hq2 z hz
      exact ⟨x, by simp [hx], hxz⟩

 theorem list_walk_between {n : ℕ} (G : SimpleGraph (Fin n)) (l : List (Fin n))
    (hne : l ≠ []) (chain : l.IsChain G.Adj) {u v : Fin n} (hu : u ∈ l) (hv : v ∈ l) :
    ∃ q : G.Walk u v, q.support ⊆ l := by
  classical
  let p := SimpleGraph.Walk.ofSupport l hne chain
  have hpu : u ∈ p.support := by simpa [p] using hu
  have hpv : v ∈ p.support := by simpa [p] using hv
  refine ⟨(p.takeUntil u hpu).reverse.append (p.takeUntil v hpv), ?_⟩
  intro x hx
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hx with hx | hx
  · have : x ∈ p.support := p.support_takeUntil_subset_support hpu (by simpa using hx)
    simpa [p] using this
  · have : x ∈ p.support := p.support_takeUntil_subset_support hpv hx
    simpa [p] using this

 noncomputable def touched {h n : ℕ} {H : SimpleGraph (Fin h)} {G : SimpleGraph (Fin n)}
    (embedding : AlmostEmbedding H G) (v : Fin n) : Finset (Fin h) := by
  classical
  exact Finset.univ.filter (fun x => ∃ e : EdgeIndex H,
    (x = e.val.1 ∨ x = e.val.2) ∧ v ∈ embedding.path e)

 theorem mem_touched {h n : ℕ} {H : SimpleGraph (Fin h)} {G : SimpleGraph (Fin n)}
    (embedding : AlmostEmbedding H G) (v : Fin n) (x : Fin h) :
    x ∈ touched embedding v ↔ ∃ e : EdgeIndex H,
      (x = e.val.1 ∨ x = e.val.2) ∧ v ∈ embedding.path e := by
  classical
  simp [touched]

 theorem endpoint_mem {h n : ℕ} {H : SimpleGraph (Fin h)} {G : SimpleGraph (Fin n)}
    (embedding : AlmostEmbedding H G) (e : EdgeIndex H) {x : Fin h}
    (hx : x = e.val.1 ∨ x = e.val.2) : embedding.vertex x ∈ embedding.path e := by
  rcases hx with rfl | rfl
  · exact List.mem_of_head? (embedding.valid e).2.1
  · exact List.mem_of_getLast? (embedding.valid e).2.2

 theorem incident_edge {h : ℕ} (H : SimpleGraph (Fin h)) {x y : Fin h} (hxy : H.Adj x y) :
    ∃ e : EdgeIndex H, (x = e.val.1 ∨ x = e.val.2) ∧ (y = e.val.1 ∨ y = e.val.2) := by
  rcases lt_or_gt_of_ne (H.ne_of_adj hxy) with h | h
  · exact ⟨⟨(x,y), h, hxy⟩, Or.inl rfl, Or.inr rfl⟩
  · exact ⟨⟨(y,x), h, hxy.symm⟩, Or.inr rfl, Or.inl rfl⟩

 theorem touched_card {h n : ℕ} (H : SimpleGraph (Fin h)) (G : SimpleGraph (Fin n))
    (embedding : AlmostEmbedding H G) (d : ℕ) (hd : ∀ v, degree H v ≤ d) (v : Fin n) :
    (touched embedding v).card ≤ 2 * d := by
  classical
  by_cases hne : (touched embedding v).Nonempty
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨e, hxe, hve⟩ := (mem_touched embedding v x).mp hx
    have hsub : touched embedding v ⊆ H.neighborFinset e.val.1 ∪ H.neighborFinset e.val.2 := by
      intro y hy
      obtain ⟨f, hyf, hvf⟩ := (mem_touched embedding v y).mp hy
      have shares : e.val.1 = f.val.1 ∨ e.val.1 = f.val.2 ∨ e.val.2 = f.val.1 ∨ e.val.2 = f.val.2 := by
        by_contra hh
        push_neg at hh
        exact embedding.disjoint e f hh.1 hh.2.1 hh.2.2.1 hh.2.2.2 v hve hvf
      have he := e.property.2
      have hes := he.symm
      have hf := f.property.2
      have hfs := hf.symm
      simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset]
      rcases hyf with rfl | rfl <;> rcases shares with hh | hh | hh | hh <;> aesop
    have hdeg (u : Fin h) : (H.neighborFinset u).card ≤ d := by
      simpa only [degree, Set.ncard_eq_toFinset_card', SimpleGraph.neighborFinset_def] using hd u
    calc
      (touched embedding v).card ≤ (H.neighborFinset e.val.1 ∪ H.neighborFinset e.val.2).card := Finset.card_le_card hsub
      _ ≤ (H.neighborFinset e.val.1).card + (H.neighborFinset e.val.2).card := Finset.card_union_le _ _
      _ ≤ 2 * d := by have h1 := hdeg e.val.1; have h2 := hdeg e.val.2; omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

end EdgeSublinearMWIS.Main.DecompositionHelpers


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
open EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.DecompositionHelpers
open EdgeSublinearMWIS.Main.GraphHelpers TreewidthApprox.Pushed
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.TreeSeparator

 theorem path_length_eq_dist {T : Type} (tree : SimpleGraph T) (htree : tree.IsTree)
    {s t : T} (p : tree.Walk s t) (hp : p.IsPath) : p.length = tree.dist s t := by
  obtain ⟨q, hq, hdist⟩ := htree.connected.exists_path_of_dist s t
  let := htree.isAcyclic.subsingleton_path s t
  have he : p = q := congrArg Subtype.val (Subsingleton.elim (⟨p,hp⟩ : tree.Path s t) ⟨q,hq⟩)
  exact he ▸ hdist

 theorem centroid {n : ℕ} {T : Type} [Fintype T] (tree : SimpleGraph T)
    (htree : tree.IsTree) (W : Finset (Fin n)) (home : Fin n → T) :
    ∃ t : T, ∀ u, tree.Adj t u →
      2 * (W.filter (fun v => tree.dist (home v) u < tree.dist (home v) t)).card ≤ W.card := by
  classical
  let F : T → ℕ := fun t => ∑ v ∈ W, tree.dist (home v) t
  have hne : (Finset.univ : Finset T).Nonempty := by
    let := htree.connected.nonempty
    exact Finset.univ_nonempty
  obtain ⟨t, ht, hmin⟩ := Finset.univ.exists_min_image F hne
  refine ⟨t, ?_⟩
  intro u hadj
  have hpoint (v : Fin n) : tree.dist (home v) u +
      2 * (if tree.dist (home v) u < tree.dist (home v) t then 1 else 0) =
      tree.dist (home v) t + 1 := by
    have h := htree.dist_eq_dist_add_one_of_adj (home v) hadj
    split_ifs <;> omega
  have hsum := Finset.sum_congr (s₁ := W) rfl (fun v hv => hpoint v)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul,
    mul_one, Finset.sum_boole] at hsum
  have hsum' : F u + 2 * (W.filter (fun v => tree.dist (home v) u < tree.dist (home v) t)).card = F t + W.card := by
    simpa [F] using hsum
  have hmin' := hmin u (Finset.mem_univ _)
  omega

 theorem away_from_root {T : Type} (tree : SimpleGraph T) (htree : tree.IsTree)
    {root u v w : T} (hadj : tree.Adj root u) (p : tree.Walk u v)
    (hp : root ∉ p.support) (q : tree.Walk v w) (hq : root ∉ q.support) :
    tree.dist w u < tree.dist w root := by
  classical
  let R := p.append q
  have hR : root ∉ R.support := by
    simpa only [R, SimpleGraph.Walk.mem_support_append_iff, not_or] using And.intro hp hq
  have hpath : (R.toPath.val.cons hadj).IsPath :=
    R.toPath.property.cons (fun h => hR (R.support_toPath_subset_support h))
  have hlen1 := path_length_eq_dist tree htree (R.toPath.val.cons hadj) hpath
  have hlen2 := path_length_eq_dist tree htree R.toPath.val R.toPath.property
  simp only [SimpleGraph.Walk.length_cons] at hlen1
  rw [SimpleGraph.dist_comm (G := tree) (u := w) (v := u),
    SimpleGraph.dist_comm (G := tree) (u := w) (v := root)]
  omega

 theorem separator_of_decomposition {n : ℕ} (G : SimpleGraph (Fin n)) {T : Type}
    [Fintype T] (tree : SimpleGraph T) (bags : T → Finset (Fin n))
    (dec : RobertsonSeymour1986.GM5.IsTreeDecomposition G tree bags) (W : Finset (Fin n)) :
    ∃ t : T, Balanced G W (W ∩ bags t) := by
  classical
  let home : Fin n → T := fun v => Classical.choose (dec.2.1 v)
  have home_mem (v : Fin n) : v ∈ bags (home v) := Classical.choose_spec (dec.2.1 v)
  obtain ⟨t, ht⟩ := centroid tree dec.1 W home
  refine ⟨t, Finset.inter_subset_left, ?_⟩
  intro D hD
  by_cases hDne : D.Nonempty
  · obtain ⟨v0, hv0⟩ := hDne
    have hsub := component_subset G W (W ∩ bags t) hD
    have hnotbag (v : Fin n) (hv : v ∈ D) : v ∉ bags t := by
      have hh := Finset.mem_sdiff.mp (hsub hv)
      intro hb
      exact hh.2 (Finset.mem_inter.mpr ⟨hh.1, hb⟩)
    have hhome : home v0 ≠ t := by
      intro h
      exact hnotbag v0 hv0 (h ▸ home_mem v0)
    obtain ⟨p0, hp0⟩ := dec.1.connected.exists_isPath t (home v0)
    cases p0 with
    | nil => exact False.elim (hhome rfl)
    | @cons _ u _ hadj p =>
      have hp : t ∉ p.support := (SimpleGraph.Walk.cons_isPath_iff hadj p).mp hp0 |>.2
      have hDside : D ⊆ W.filter (fun v => tree.dist (home v) u < tree.dist (home v) t) := by
        intro v hv
        refine Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp (hsub hv)).1, ?_⟩
        have hreach : AvoidReach G ((W ∩ bags t) ∪ (Finset.univ \ W)) v0 v := by
          obtain ⟨z, hz, hDz⟩ := Finset.mem_image.mp hD
          have hv0' : v0 ∈ avoidComp G ((W ∩ bags t) ∪ (Finset.univ \ W)) z := hDz ▸ hv0
          have hv' : v ∈ avoidComp G ((W ∩ bags t) ∪ (Finset.univ \ W)) z := hDz ▸ hv
          have heq := comp_eq G _ hv0'
          exact (comp_mem G _ v0 v).mp (heq ▸ hv')
        obtain ⟨qG, hqG⟩ := hreach
        obtain ⟨qT, hqT⟩ := walk_bags G tree bags dec qG (home_mem v0) (home_mem v)
        have havoid : t ∉ qT.support := by
          intro hm
          obtain ⟨x, hx, hxt⟩ := hqT t hm
          have hxx := hqG x hx
          have hxW : x ∈ W := by
            by_contra h
            exact hxx (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩))
          exact hxx (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxW, hxt⟩))
        exact away_from_root tree dec.1 hadj p hp qT havoid
      have hcard := Finset.card_le_card hDside
      have hhalf := ht u hadj
      omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hDne]

end EdgeSublinearMWIS.Main.TreeSeparator


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
open EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.TreeSeparator
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
  obtain ⟨T, inst, tree, bags, dec, hsize⟩ := treewidth_witness G
  letI := inst
  apply Nat.sInf_le
  intro W
  obtain ⟨t, hbal⟩ := separator_of_decomposition G tree bags dec W
  exact ⟨W ∩ bags t, hbal, (Finset.card_le_card Finset.inter_subset_right).trans (hsize t)⟩

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
