-- Prove2me | solution 1 for EdgeSublinearMWIS.Main.path_system_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T18:17:48.135862+00:00
-- url     : https://prove2.me/submissions/25c20139-4dec-4d67-b818-dcf04e47dbe7

import Definitions.Def_EdgeSublinearMWIS_Main_Paths
import Definitions.Def_EdgeSublinearMWIS_Main_Graphs
import Theorems.Thm_EdgeSublinearMWIS_Main_treewidth_separator
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Theorems.Thm_EdgeSublinearMWIS_Main_lemma_10

noncomputable section

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
end

noncomputable section

open scoped BigOperators
open EdgeSublinearMWIS.Main
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.EdgeCounting

 theorem edgeCount_eq {n : ℕ} (G : SimpleGraph (Fin n)) : edgeCount G = G.edgeSet.ncard := by
  classical
  rw [edgeCount, Set.ncard_eq_toFinset_card']
  change ((Finset.univ : Finset (Fin n × Fin n)).filter
    (fun e => e.1 < e.2 ∧ G.Adj e.1 e.2)).card = G.edgeFinset.card
  apply Finset.card_bij (fun e he => s(e.1,e.2))
  · intro e he
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using (Finset.mem_filter.mp he).2.2
  · intro e he f hf hEq
    have he' := (Finset.mem_filter.mp he).2.1
    have hf' := (Finset.mem_filter.mp hf).2.1
    rcases Sym2.eq_iff.mp hEq with hEq | hEq
    · exact Prod.ext hEq.1 hEq.2
    · have h1 := congrArg Fin.val hEq.1
      have h2 := congrArg Fin.val hEq.2
      have heV := he'
      have hfV := hf'
      simp only [Fin.lt_def] at heV hfV
      omega
  · intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      have hadj : G.Adj u v := by simpa using he
      rcases lt_or_gt_of_ne (G.ne_of_adj hadj) with h | h
      · exact ⟨(u,v), by simp [h, hadj], rfl⟩
      · exact ⟨(v,u), by simp [h, hadj.symm], Sym2.eq_swap⟩

end EdgeSublinearMWIS.Main.EdgeCounting
end

noncomputable section

open scoped BigOperators
open EdgeSublinearMWIS.Main
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.StructuralHelpers

 theorem blowup_of_projection {n m : ℕ} (C : GraphClass) (G : SimpleGraph (Fin n))
    (hC : Hereditary C) (hG : C n G) (H : SimpleGraph (Fin m)) (p : Fin m → Fin n)
    (hAdj : ∀ u v, H.Adj u v ↔ G.Adj (p u) (p v)) : BlowupClass C m H := by
  classical
  let V := {v : Fin n // v ∈ Set.range p}
  let r := Fintype.card V
  let e : V ≃ Fin r := Fintype.equivFin V
  let inc : Fin r ↪ Fin n :=
    ⟨fun v => (e.symm v).val, Subtype.val_injective.comp e.symm.injective⟩
  let G0 := G.comap inc
  have hG0 : C r G0 := hC G G0 inc hG (fun u v => Iff.rfl)
  let f : Fin m → Fin r := fun u => e ⟨p u, Set.mem_range_self u⟩
  refine ⟨r, G0, hG0, f, ?_, ?_⟩
  · intro v
    obtain ⟨u, hu⟩ := (e.symm v).property
    refine ⟨u, ?_⟩
    have hh : (⟨p u, Set.mem_range_self u⟩ : V) = e.symm v := Subtype.ext hu
    change e _ = v
    rw [hh]
    exact e.apply_symm_apply v
  · intro u v
    change H.Adj u v ↔ G.Adj (inc (f u)) (inc (f v))
    simpa only [inc, f, Function.Embedding.coeFn_mk, Equiv.symm_apply_apply] using hAdj u v

 theorem blowup_hereditary (C : GraphClass) (hC : Hereditary C) : Hereditary (BlowupClass C) := by
  intro n m H H' inc hH hind
  obtain ⟨r, G, hG, p, hp, hAdj⟩ := hH
  exact blowup_of_projection C G hC hG H' (fun v => p (inc v))
    (fun u v => (hind u v).trans (hAdj (inc u) (inc v)))

end EdgeSublinearMWIS.Main.StructuralHelpers
end

noncomputable section

open scoped BigOperators Classical
open EdgeSublinearMWIS.Main
open EdgeSublinearMWIS.Main.EdgeCounting
open RobertsonSeymour1986.GM5
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BlowupDecomposition

/-- Leaf attachment; construction and degree-count proof follow the paper-linked
Lax263307Proofs.TreeExtensions (commit 68b2d26), adapted to this mission's API. -/
def attachLeaves {α β : Type} (T : SimpleGraph α) (root : α) : SimpleGraph (α ⊕ β) where
  Adj
    | .inl a, .inl b => T.Adj a b
    | .inl a, .inr _ => a = root
    | .inr _, .inl b => b = root
    | .inr _, .inr _ => False
  symm := ⟨by intro a b h; cases a <;> cases b <;> simp_all [T.adj_comm]⟩
  loopless := ⟨by intro a; cases a <;> simp⟩

 theorem degree_as_sum {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) :
    G.degree v = ∑ u, if G.Adj v u then 1 else 0 := by
  classical
  rw [SimpleGraph.degree, G.neighborFinset_eq_filter]
  simp

 theorem attachLeaves_tree {α β : Type} [Fintype α] [Fintype β]
    (T : SimpleGraph α) (root : α) (hT : T.IsTree) : (attachLeaves (β := β) T root).IsTree := by
  classical
  let H := attachLeaves (β := β) T root
  let inclusion : T →g H := ⟨Sum.inl, fun h => h⟩
  have hroot : ∀ a : α ⊕ β, H.Reachable a (.inl root) := by
    intro a
    cases a with
    | inl a => exact (hT.connected a root).map inclusion
    | inr b => exact SimpleGraph.Adj.reachable (show H.Adj (.inr b) (.inl root) from rfl)
  have : Nonempty (α ⊕ β) := ⟨.inl root⟩
  have hconn : H.Connected := ⟨fun a b => (hroot a).trans (hroot b).symm⟩
  have hleft (a : α) : H.degree (.inl a) = T.degree a + if a = root then Fintype.card β else 0 := by
    rw [degree_as_sum, Fintype.sum_sum_type, degree_as_sum]
    simp only [H, attachLeaves]
    split_ifs <;> simp_all
  have hright (b : β) : H.degree (.inr b) = 1 := by
    rw [degree_as_sum, Fintype.sum_sum_type]
    simp [H, attachLeaves, eq_comm]
  have hsum : (∑ v, H.degree v) = (∑ a, T.degree a) + 2 * Fintype.card β := by
    rw [Fintype.sum_sum_type]
    simp_rw [hleft, hright]
    simp [Finset.sum_add_distrib]
    omega
  change H.IsTree
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hconn, ?_⟩
  have hcount := hT.card_edgeFinset
  have hhand := H.sum_degrees_eq_twice_card_edges
  rw [hsum, T.sum_degrees_eq_twice_card_edges] at hhand
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_sum,
    ← SimpleGraph.edgeFinset_card]
  omega

 theorem degree_eq {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : degree G v = G.degree v := by
  classical
  rw [degree, Set.ncard_eq_toFinset_card']
  rfl

 noncomputable def highDegree {m : ℕ} (H : SimpleGraph (Fin m)) (s : ℕ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun v => s < H.degree v)

 theorem highDegree_card {m : ℕ} (H : SimpleGraph (Fin m)) (s : ℕ) :
    s * (highDegree H s).card ≤ 2 * edgeCount H := by
  classical
  calc
    s * (highDegree H s).card = ∑ _v ∈ highDegree H s, s := by simp [Nat.mul_comm]
    _ ≤ ∑ v ∈ highDegree H s, H.degree v := Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2.le)
    _ ≤ ∑ v, H.degree v := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
    _ = 2 * edgeCount H := by rw [edgeCount_eq, SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard]

 noncomputable def active {m : ℕ} (H : SimpleGraph (Fin m)) (s : ℕ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun v => v ∉ highDegree H s ∧ ∃ u, u ∉ highDegree H s ∧ H.Adj v u)

 theorem active_fiber_bound {n m : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m))
    (f : Fin m → Fin n) (hAdj : ∀ u v, H.Adj u v ↔ G.Adj (f u) (f v)) (s : ℕ) (v : Fin n) :
    ((active H s).filter (fun u => f u = v)).card ≤ s := by
  classical
  by_cases hne : ((active H s).filter (fun u => f u = v)).Nonempty
  · obtain ⟨u, hu⟩ := hne
    have huv : f u = v := (Finset.mem_filter.mp hu).2
    obtain ⟨huS, w, hwS, huw⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2
    have hdeg : H.degree w ≤ s := by simpa [highDegree] using hwS
    apply le_trans ?_ hdeg
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro z hz
    have hzv : f z = v := (Finset.mem_filter.mp hz).2
    apply (SimpleGraph.mem_neighborFinset H w z).mpr
    apply (hAdj w z).mpr
    simpa only [hzv, ← huv] using (hAdj w u).mp huw.symm
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

 theorem transfer_bound {n m : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m))
    (f : Fin m → Fin n) (hAdj : ∀ u v, H.Adj u v ↔ G.Adj (f u) (f v))
    {T : Type} [Fintype T] (tree : SimpleGraph T) (bags : T → Finset (Fin n))
    (dec : IsTreeDecomposition G tree bags) (w s : ℕ) (hsize : ∀ t, (bags t).card ≤ w + 1) :
    ∃ (newTree : SimpleGraph (T ⊕ Fin m)) (newBags : T ⊕ Fin m → Finset (Fin m)),
      IsTreeDecomposition H newTree newBags ∧
      ∀ t, (newBags t).card ≤ (highDegree H s).card + max 1 (s * (w + 1)) := by
  classical
  let S := highDegree H s
  let A := active H s
  let root : T := Classical.choice dec.1.connected.nonempty
  let newTree := attachLeaves (β := Fin m) tree root
  have htree : newTree.IsTree := attachLeaves_tree tree root dec.1
  let newBags : T ⊕ Fin m → Finset (Fin m) := fun t =>
    S ∪ match t with
    | .inl t => A.filter (fun v => f v ∈ bags t)
    | .inr v => if v ∈ A then ∅ else {v}
  have mem_old (t : T) (v : Fin m) : v ∈ newBags (.inl t) ↔ v ∈ S ∨ v ∈ A ∧ f v ∈ bags t := by
    simp [newBags]
  have mem_leaf (u v : Fin m) : v ∈ newBags (.inr u) ↔ v ∈ S ∨ v = u ∧ v ∉ A := by
    by_cases hu : u ∈ A <;> simp [newBags, hu] <;> aesop
  have active_notS {v : Fin m} (hv : v ∈ A) : v ∉ S := (Finset.mem_filter.mp hv).2.1
  have hcover (v : Fin m) : ∃ t, v ∈ newBags t := by
    by_cases hvS : v ∈ S
    · exact ⟨.inl root, (mem_old root v).mpr (Or.inl hvS)⟩
    · by_cases hvA : v ∈ A
      · obtain ⟨t, ht⟩ := dec.2.1 (f v)
        exact ⟨.inl t, (mem_old t v).mpr (Or.inr ⟨hvA, ht⟩)⟩
      · exact ⟨.inr v, (mem_leaf v v).mpr (Or.inr ⟨rfl, hvA⟩)⟩
  refine ⟨newTree, newBags, ⟨htree, hcover, ?_, ?_⟩, ?_⟩
  · intro u v huv
    by_cases huS : u ∈ S
    · obtain ⟨t, ht⟩ := hcover v
      exact ⟨t, Finset.mem_union_left _ huS, ht⟩
    · by_cases hvS : v ∈ S
      · obtain ⟨t, ht⟩ := hcover u
        exact ⟨t, ht, Finset.mem_union_left _ hvS⟩
      · have huA : u ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, huS, v, hvS, huv⟩
        have hvA : v ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvS, u, huS, huv.symm⟩
        obtain ⟨t, hut, hvt⟩ := dec.2.2.1 (f u) (f v) ((hAdj u v).mp huv)
        exact ⟨.inl t, (mem_old t u).mpr (Or.inr ⟨huA, hut⟩), (mem_old t v).mpr (Or.inr ⟨hvA, hvt⟩)⟩
  · intro a b c p hp hm v hv
    by_cases hvS : v ∈ S
    · exact Finset.mem_union_left _ hvS
    · have hva := (Finset.mem_inter.mp hv).1
      have hvc := (Finset.mem_inter.mp hv).2
      by_cases hvA : v ∈ A
      · have old_node (t : T ⊕ Fin m) (ht : v ∈ newBags t) : ∃ i : T, t = .inl i ∧ f v ∈ bags i := by
          cases t with
          | inl i => exact ⟨i, rfl, ((mem_old i v).mp ht).resolve_left hvS |>.2⟩
          | inr u => have hh := ((mem_leaf u v).mp ht).resolve_left hvS; exact False.elim (hh.2 hvA)
        obtain ⟨a0, rfl, hfa⟩ := old_node a hva
        obtain ⟨c0, rfl, hfc⟩ := old_node c hvc
        obtain ⟨q, hq⟩ := dec.1.connected.exists_isPath a0 c0
        let incl : tree →g newTree := ⟨Sum.inl, fun h => h⟩
        have hqmap : (q.map incl).IsPath := hq.map Sum.inl_injective
        let := htree.isAcyclic.subsingleton_path (.inl a0) (.inl c0)
        have heq : p = q.map incl := congrArg Subtype.val (Subsingleton.elim (⟨p,hp⟩ : newTree.Path (.inl a0) (.inl c0)) ⟨q.map incl,hqmap⟩)
        rw [heq, SimpleGraph.Walk.support_map] at hm
        obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hm
        apply (mem_old b0 v).mpr
        exact Or.inr ⟨hvA, dec.2.2.2 a0 b0 c0 q hq hb0 (Finset.mem_inter.mpr ⟨hfa, hfc⟩)⟩
      · have leaf_node (t : T ⊕ Fin m) (ht : v ∈ newBags t) : t = .inr v := by
          cases t with
          | inl i => have hh := ((mem_old i v).mp ht).resolve_left hvS; exact False.elim (hvA hh.1)
          | inr u => have hh := ((mem_leaf u v).mp ht).resolve_left hvS; exact congrArg Sum.inr hh.1.symm
        have ha := leaf_node a hva
        have hc := leaf_node c hvc
        subst a
        subst c
        let := htree.isAcyclic.subsingleton_path (.inr v) (.inr v)
        have heq : p = .nil := congrArg Subtype.val (Subsingleton.elim (⟨p,hp⟩ : newTree.Path (.inr v) (.inr v)) ⟨.nil, SimpleGraph.Walk.IsPath.nil⟩)
        rw [heq] at hm
        have hb : b = .inr v := by simpa using hm
        subst b
        exact hva
  · intro t
    cases t with
    | inl i =>
      have hc : (A.filter (fun v => f v ∈ bags i)).card ≤ s * (w + 1) := by
        rw [← Finset.sum_card_fiberwise_eq_card_filter]
        calc
          _ ≤ ∑ _v ∈ bags i, s := Finset.sum_le_sum (fun v hv => active_fiber_bound G H f hAdj s v)
          _ = (bags i).card * s := by simp
          _ ≤ (w + 1) * s := Nat.mul_le_mul_right _ (hsize i)
          _ = s * (w + 1) := Nat.mul_comm _ _
      exact (Finset.card_union_le S _).trans (Nat.add_le_add_left (hc.trans (le_max_right _ _)) _)
    | inr v =>
      have hc : (if v ∈ A then (∅ : Finset (Fin m)) else {v}).card ≤ 1 := by split_ifs <;> simp
      exact (Finset.card_union_le S _).trans (Nat.add_le_add_left (hc.trans (le_max_left _ _)) _)

 theorem treewidth_witness {n : ℕ} (G : SimpleGraph (Fin n)) : TreewidthLE G (PlantedSubgraphLD.tw G) := by
  have hne : {w : ℕ | TreewidthLE G w}.Nonempty := by
    refine ⟨n, PUnit, inferInstance, ⊥, (fun _ => Finset.univ), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · exact ⟨SimpleGraph.Connected.of_subsingleton, by simp⟩
      · intro v; exact ⟨PUnit.unit, Finset.mem_univ _⟩
      · intro u v h; exact ⟨PUnit.unit, Finset.mem_univ _, Finset.mem_univ _⟩
      · intro s s' s'' p hp hm; exact Finset.subset_univ _
    · intro s; simp
  exact Nat.sInf_mem hne

 theorem treewidth_zero {m : ℕ} (H : SimpleGraph (Fin m)) (hz : edgeCount H = 0) :
    PlantedSubgraphLD.tw H = 0 := by
  have hH : H = ⊥ := by
    apply SimpleGraph.edgeFinset_eq_empty.mp
    apply Finset.card_eq_zero.mp
    have hh := hz
    rw [edgeCount_eq] at hh
    simpa only [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard] using hh
  have hS : highDegree H 0 = ∅ := by simp [highDegree, hH]
  obtain ⟨T, inst, tree, bags, dec, size⟩ := treewidth_witness H
  let := inst
  obtain ⟨tr, bs, hd, hsize⟩ := transfer_bound H H id (fun _ _ => Iff.rfl) tree bags dec (PlantedSubgraphLD.tw H) 0 size
  have hw : TreewidthLE H 0 := by
    refine ⟨T ⊕ Fin m, inferInstance, tr, bs, hd, ?_⟩
    intro t
    simpa [hS] using hsize t
  have ht : PlantedSubgraphLD.tw H ≤ 0 := Nat.sInf_le hw
  omega

 theorem power_bound {n m : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m))
    (f : Fin m → Fin n) (hAdj : ∀ u v, H.Adj u v ↔ G.Adj (f u) (f v))
    (w : ℕ) (b c : ℝ) (hb : 0 ≤ b) (hb1 : b < 1) (hc : 0 < c)
    (hm : 1 ≤ edgeCount H) (hw : TreewidthLE G w)
    (hbound : (w + 1 : ℕ) ≤ c * (edgeCount H : ℝ) ^ b) :
    (PlantedSubgraphLD.tw H : ℝ) ≤ (3 + 2 * c) * (edgeCount H : ℝ) ^ ((1 + b) / 2) := by
  let M : ℝ := edgeCount H
  let α := (1 - b) / 2
  let β := (1 + b) / 2
  let q := M ^ α
  let t := M ^ β
  let s := Nat.ceil q
  have hM : 1 ≤ M := by dsimp [M]; exact_mod_cast hm
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hα : 0 ≤ α := by dsimp [α]; linarith
  have hβ : 0 ≤ β := by dsimp [β]; linarith
  have hq : 1 ≤ q := Real.one_le_rpow hM hα
  have ht : 1 ≤ t := Real.one_le_rpow hM hβ
  have hqs : q ≤ (s : ℝ) := Nat.le_ceil q
  have hs : (s : ℝ) ≤ 2 * q := by
    have hceil := (Nat.ceil_lt_add_one (show 0 ≤ q by linarith)).le
    change (s : ℝ) ≤ q + 1 at hceil
    linarith
  have hqt : q * t = M := by
    dsimp [q, t]
    rw [← Real.rpow_add hMpos]
    have he : α + β = 1 := by dsimp [α, β]; ring
    rw [he, Real.rpow_one]
  have hqb : q * M ^ b = t := by
    dsimp [q, t]
    rw [← Real.rpow_add hMpos]
    have he : α + b = β := by dsimp [α, β]; ring
    rw [he]
  have hhigh : ((highDegree H s).card : ℝ) ≤ 2 * t := by
    have hdegree : (s : ℝ) * (highDegree H s).card ≤ 2 * M := by
      dsimp [M]
      exact_mod_cast highDegree_card H s
    have hqX : q * (highDegree H s).card ≤ (s : ℝ) * (highDegree H s).card :=
      mul_le_mul_of_nonneg_right hqs (Nat.cast_nonneg _)
    have hmul : q * (highDegree H s).card ≤ q * (2 * t) := by nlinarith [hqt]
    exact (mul_le_mul_iff_right₀ (show 0 < q by linarith)).mp hmul
  have hlift : (s : ℝ) * (w + 1 : ℕ) ≤ 2 * c * t := by
    calc
      (s : ℝ) * (w + 1 : ℕ) ≤ (2 * q) * (c * M ^ b) :=
        mul_le_mul hs hbound (Nat.cast_nonneg _) (by positivity)
      _ = 2 * c * t := by rw [← hqb]; ring
  obtain ⟨T, inst, tree, bags, dec, size⟩ := hw
  let := inst
  obtain ⟨tr, bs, hd, hsize⟩ := transfer_bound G H f hAdj tree bags dec w s size
  let B := (highDegree H s).card + max 1 (s * (w + 1))
  have hwidth : TreewidthLE H B := by
    refine ⟨T ⊕ Fin m, inferInstance, tr, bs, hd, ?_⟩
    intro j
    exact (hsize j).trans (Nat.le_succ _)
  have htw : (PlantedSubgraphLD.tw H : ℝ) ≤ B := by exact_mod_cast (show PlantedSubgraphLD.tw H ≤ B from Nat.sInf_le hwidth)
  have hB : (B : ℝ) = (highDegree H s).card + max 1 ((s : ℝ) * (w + 1 : ℕ)) := by
    simp [B, Nat.cast_max, Nat.cast_mul]
  rw [hB] at htw
  have hmax : max 1 ((s : ℝ) * (w + 1 : ℕ)) ≤ 1 + (s : ℝ) * (w + 1 : ℕ) :=
    max_le (le_add_of_nonneg_right (by positivity)) (by linarith)
  change (PlantedSubgraphLD.tw H : ℝ) ≤ (3 + 2 * c) * t
  nlinarith

end EdgeSublinearMWIS.Main.BlowupDecomposition
end

noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.PartialDecomposition

 def DecompositionOn {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n))
    {T : Type} (tree : SimpleGraph T) (bags : T → Finset (Fin n)) : Prop :=
  tree.IsTree ∧ (∀ v∈U,∃ t,v∈bags t) ∧
    (∀ u∈U,∀ v∈U,G.Adj u v → ∃ t,u∈bags t ∧ v∈bags t) ∧
    ∀ (s t r : T) (p : tree.Walk s r),p.IsPath → t∈p.support → bags s ∩ bags r ⊆ bags t

 theorem vertex_walk {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n))
    {T : Type} (tree : SimpleGraph T) (bags : T → Finset (Fin n)) (dec : DecompositionOn G U tree bags)
    {s t : T} {v : Fin n} (hs : v∈bags s) (ht : v∈bags t) :
    ∃ q : tree.Walk s t,∀ z∈q.support,v∈bags z := by
  obtain ⟨q,hq⟩ := dec.1.connected.exists_isPath s t
  exact ⟨q,fun z hz => dec.2.2.2 s z t q hq hz (Finset.mem_inter.mpr ⟨hs,ht⟩)⟩

 theorem walk_bags {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n))
    {T : Type} (tree : SimpleGraph T) (bags : T → Finset (Fin n)) (dec : DecompositionOn G U tree bags)
    {u v : Fin n} (p : G.Walk u v) (hU : ∀ z∈p.support,z∈U)
    {s t : T} (hs : u∈bags s) (ht : v∈bags t) :
    ∃ q : tree.Walk s t,∀ z∈q.support,∃ x∈p.support,x∈bags z := by
  induction p generalizing s with
  | nil =>
    obtain ⟨q,hq⟩ := vertex_walk G U tree bags dec hs ht
    exact ⟨q,fun z hz => ⟨_,by simp,hq z hz⟩⟩
  | @cons u v w hadj p ih =>
    have huU := hU u (by simp)
    have hvU := hU v (by simp)
    obtain ⟨b,hub,hvb⟩ := dec.2.2.1 u huU v hvU hadj
    obtain ⟨q1,hq1⟩ := vertex_walk G U tree bags dec hs hub
    obtain ⟨q2,hq2⟩ := ih (fun z hz => hU z (by simp [hz])) hvb ht
    refine ⟨q1.append q2,?_⟩
    intro z hz
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hz with hz | hz
    · exact ⟨u,by simp,hq1 z hz⟩
    · obtain ⟨x,hx,hxb⟩ := hq2 z hz
      exact ⟨x,by simp [hx],hxb⟩

 def numbering {n : ℕ} (U : Finset (Fin n)) : Fin (Fintype.card U) ↪ Fin n where
  toFun i := ((Fintype.equivFin U).symm i).val
  inj' := by
    intro i j hij
    apply (Fintype.equivFin U).symm.injective
    exact Subtype.ext hij

 theorem numbering_range {n : ℕ} (U : Finset (Fin n)) (v : Fin n) : v∈U ↔ ∃ i,numbering U i=v := by
  constructor
  · intro hv
    refine ⟨Fintype.equivFin U ⟨v,hv⟩,?_⟩
    change (((Fintype.equivFin U).symm ((Fintype.equivFin U) ⟨v,hv⟩)) : U).val = v
    rw [Equiv.symm_apply_apply]
  · rintro ⟨i,rfl⟩
    exact ((Fintype.equivFin U).symm i).property

 def induced {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) : SimpleGraph (Fin (Fintype.card U)) :=
  G.comap (numbering U)

 theorem induced_mem {n : ℕ} (C : GraphClass) (her : Hereditary C) (G : SimpleGraph (Fin n))
    (U : Finset (Fin n)) (hC : C n G) : C (Fintype.card U) (induced G U) :=
  her G (induced G U) (numbering U) hC (by intro u v; rfl)

 theorem lift_decomposition {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n))
    {T : Type} (tree : SimpleGraph T) (bags : T → Finset (Fin (Fintype.card U)))
    (dec : RobertsonSeymour1986.GM5.IsTreeDecomposition (induced G U) tree bags) :
    DecompositionOn G U tree (fun t => (bags t).map (numbering U)) := by
  refine ⟨dec.1,?_,?_,?_⟩
  · intro v hv
    obtain ⟨i,hi⟩ := (numbering_range U v).mp hv
    obtain ⟨t,ht⟩ := dec.2.1 i
    exact ⟨t,Finset.mem_map.mpr ⟨i,ht,hi⟩⟩
  · intro u hu v hv huv
    obtain ⟨i,hi⟩ := (numbering_range U u).mp hu
    obtain ⟨j,hj⟩ := (numbering_range U v).mp hv
    have hAdj : (induced G U).Adj i j := by change G.Adj (numbering U i) (numbering U j); simpa only [hi,hj] using huv
    obtain ⟨t,hit,hjt⟩ := dec.2.2.1 i j hAdj
    exact ⟨t,Finset.mem_map.mpr ⟨i,hit,hi⟩,Finset.mem_map.mpr ⟨j,hjt,hj⟩⟩
  · intro s t r p hp hm v hv
    obtain ⟨i,hi,hiv⟩ := Finset.mem_map.mp (Finset.mem_inter.mp hv).1
    obtain ⟨j,hj,hjv⟩ := Finset.mem_map.mp (Finset.mem_inter.mp hv).2
    have hij := (numbering U).injective (hiv.trans hjv.symm)
    subst j
    exact Finset.mem_map.mpr ⟨i,dec.2.2.2 s t r p hp hm (Finset.mem_inter.mpr ⟨hi,hj⟩),hiv⟩

end EdgeSublinearMWIS.Main.PartialDecomposition
end

noncomputable section

open scoped BigOperators Classical
open EdgeSublinearMWIS.Main.DecompositionHelpers
open EdgeSublinearMWIS.Main.BlowupDecomposition
open RobertsonSeymour1986.GM5
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.PartialDecomposition

 def deletedEndpoints {h : ℕ} (H : SimpleGraph (Fin h)) (R : Finset (EdgeIndex H)) : Finset (Fin h) :=
  (Finset.univ \ R).biUnion (fun e => {e.val.1,e.val.2})

 theorem deleted_card {h : ℕ} (H : SimpleGraph (Fin h)) (R : Finset (EdgeIndex H)) :
    (deletedEndpoints H R).card ≤ 2 * (Finset.univ \ R).card := by
  calc
    _ ≤ ∑ e ∈ Finset.univ \ R, ({e.val.1,e.val.2} : Finset (Fin h)).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ Finset.univ \ R, 2 := Finset.sum_le_sum (fun _ _ => by simpa using (Finset.card_insert_le _ ({_} : Finset (Fin h))))
    _ = _ := by simp [Nat.mul_comm]

 theorem incident_retained {h : ℕ} (H : SimpleGraph (Fin h)) (R : Finset (EdgeIndex H))
    {x : Fin h} (hx : x ∉ deletedEndpoints H R) (e : EdgeIndex H)
    (he : x=e.val.1 ∨ x=e.val.2) : e∈R := by
  by_contra hn
  apply hx
  apply Finset.mem_biUnion.mpr
  exact ⟨e,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hn⟩,by simp only [Finset.mem_insert,Finset.mem_singleton]; exact he⟩

 theorem transfer {h n : ℕ} (H : SimpleGraph (Fin h)) (G : SimpleGraph (Fin n))
    (E : AlmostEmbedding H G) (R : Finset (EdgeIndex H)) (U : Finset (Fin n))
    (hU : ∀ e∈R,∀ v∈E.path e,v∈U)
    {T : Type} [Fintype T] (tree : SimpleGraph T) (bags : T → Finset (Fin n))
    (dec : DecompositionOn G U tree bags) (d w : ℕ) (hd : ∀v,degree H v ≤ d)
    (size : ∀ t,(bags t).card ≤ w) :
    ∃ (tr : SimpleGraph (T ⊕ Fin h)) (bs : T ⊕ Fin h → Finset (Fin h)),
      IsTreeDecomposition H tr bs ∧ ∀ t,(bs t).card ≤ (deletedEndpoints H R).card + max 1 (2*d*w) := by
  let S := deletedEndpoints H R
  let A : Finset (Fin h) := Finset.univ.filter (fun x => ∃ y,H.Adj x y)
  let root : T := Classical.choice dec.1.connected.nonempty
  let tr := attachLeaves (β := Fin h) tree root
  have htree : tr.IsTree := attachLeaves_tree tree root dec.1
  let bs : T ⊕ Fin h → Finset (Fin h) := fun t => S ∪ match t with
    | .inl t => (bags t).biUnion (touched E)
    | .inr x => if x∈A then ∅ else {x}
  have mem_old (t : T) (x : Fin h) : x∈bs (.inl t) ↔ x∈S ∨
      ∃ v∈bags t,∃ e : EdgeIndex H,(x=e.val.1 ∨ x=e.val.2) ∧ v∈E.path e := by
    simp [bs,mem_touched]
  have mem_leaf (u x : Fin h) : x∈bs (.inr u) ↔ x∈S ∨ x=u ∧ x∉A := by
    by_cases hu : u∈A <;> simp [bs,hu] <;> aesop
  have touched_active {x : Fin h} {e : EdgeIndex H} (he : x=e.val.1 ∨ x=e.val.2) : x∈A := by
    rcases he with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,e.val.2,e.property.2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,e.val.1,e.property.2.symm⟩
  have cover (x : Fin h) : ∃ t,x∈bs t := by
    by_cases hxS : x∈S
    · exact ⟨.inl root,(mem_old _ _).mpr (Or.inl hxS)⟩
    by_cases hxA : x∈A
    · obtain ⟨y,hxy⟩ := (Finset.mem_filter.mp hxA).2
      obtain ⟨e,hxe,_⟩ := incident_edge H hxy
      have heR := incident_retained H R hxS e hxe
      have hvU := hU e heR (E.vertex x) (endpoint_mem E e hxe)
      obtain ⟨t,ht⟩ := dec.2.1 _ hvU
      exact ⟨.inl t,(mem_old _ _).mpr (Or.inr ⟨_,ht,e,hxe,endpoint_mem E e hxe⟩)⟩
    · exact ⟨.inr x,(mem_leaf _ _).mpr (Or.inr ⟨rfl,hxA⟩)⟩
  refine ⟨tr,bs,⟨htree,cover,?_,?_⟩,?_⟩
  · intro x y hxy
    by_cases hxS : x∈S
    · obtain ⟨t,ht⟩ := cover y
      exact ⟨t,Finset.mem_union_left _ hxS,ht⟩
    by_cases hyS : y∈S
    · obtain ⟨t,ht⟩ := cover x
      exact ⟨t,ht,Finset.mem_union_left _ hyS⟩
    obtain ⟨e,hxe,hye⟩ := incident_edge H hxy
    have heR := incident_retained H R hxS e hxe
    have hvU := hU e heR (E.vertex x) (endpoint_mem E e hxe)
    obtain ⟨t,ht⟩ := dec.2.1 _ hvU
    exact ⟨.inl t,(mem_old _ _).mpr (Or.inr ⟨_,ht,e,hxe,endpoint_mem E e hxe⟩),
      (mem_old _ _).mpr (Or.inr ⟨_,ht,e,hye,endpoint_mem E e hxe⟩)⟩
  · intro a b c p hp hm x hx
    by_cases hxS : x∈S
    · exact Finset.mem_union_left _ hxS
    have hxa := (Finset.mem_inter.mp hx).1
    have hxc := (Finset.mem_inter.mp hx).2
    by_cases hxA : x∈A
    · have old_node (t : T ⊕ Fin h) (ht : x∈bs t) : ∃ i : T,t=.inl i := by
        cases t with
        | inl i => exact ⟨i,rfl⟩
        | inr u => exact False.elim ((((mem_leaf _ _).mp ht).resolve_left hxS).2 hxA)
      obtain ⟨a0,rfl⟩ := old_node a hxa
      obtain ⟨c0,rfl⟩ := old_node c hxc
      obtain ⟨v,hv,e,hxe,hve⟩ := ((mem_old _ _).mp hxa).resolve_left hxS
      obtain ⟨u,hu,f,hxf,huf⟩ := ((mem_old _ _).mp hxc).resolve_left hxS
      have heR := incident_retained H R hxS e hxe
      have hfR := incident_retained H R hxS f hxf
      obtain ⟨q1,hq1⟩ := list_walk_between G (E.path e) (E.valid e).1.1 (E.valid e).1.2.2.2 hve (endpoint_mem E e hxe)
      obtain ⟨q2,hq2⟩ := list_walk_between G (E.path f) (E.valid f).1.1 (E.valid f).1.2.2.2 (endpoint_mem E f hxf) huf
      have hwalkU : ∀ z∈(q1.append q2).support,z∈U := by
        intro z hz
        rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hz with hz | hz
        · exact hU e heR z (hq1 hz)
        · exact hU f hfR z (hq2 hz)
      obtain ⟨q,hq⟩ := walk_bags G U tree bags dec (q1.append q2) hwalkU hv hu
      let incl : tree →g tr := ⟨Sum.inl,fun h => h⟩
      have hm' := path_support_subset_walk tr htree.isAcyclic p hp (q.map incl) hm
      rw [SimpleGraph.Walk.support_map] at hm'
      obtain ⟨b0,hb0,rfl⟩ := List.mem_map.mp hm'
      obtain ⟨z,hz,hzb⟩ := hq b0 hb0
      apply (mem_old _ _).mpr
      refine Or.inr ⟨z,hzb,?_⟩
      rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hz with hz | hz
      · exact ⟨e,hxe,hq1 hz⟩
      · exact ⟨f,hxf,hq2 hz⟩
    · have leaf_node (t : T ⊕ Fin h) (ht : x∈bs t) : t=.inr x := by
        cases t with
        | inl i =>
          obtain ⟨v,hv,e,he,hve⟩ := ((mem_old _ _).mp ht).resolve_left hxS
          exact False.elim (hxA (touched_active he))
        | inr u => exact congrArg Sum.inr (((mem_leaf _ _).mp ht).resolve_left hxS).1.symm
      have ha := leaf_node a hxa
      have hc := leaf_node c hxc
      subst a
      subst c
      have hm' := path_support_subset_walk tr htree.isAcyclic p hp (.nil : tr.Walk (.inr x) (.inr x)) hm
      have hb : b=.inr x := by simpa using hm'
      subst b
      exact hxa
  · intro t
    cases t with
    | inl i =>
      have hc : ((bags i).biUnion (touched E)).card ≤ 2*d*w := by
        calc
          _ ≤ ∑ v∈bags i,(touched E v).card := Finset.card_biUnion_le
          _ ≤ ∑ _v∈bags i,2*d := Finset.sum_le_sum (fun v hv => touched_card H G E d hd v)
          _ = (bags i).card*(2*d) := by simp
          _ ≤ w*(2*d) := Nat.mul_le_mul_right _ (size i)
          _ = _ := Nat.mul_comm _ _
      exact (Finset.card_union_le S _).trans (Nat.add_le_add_left (hc.trans (le_max_right _ _)) _)
    | inr u =>
      have hc : (if u∈A then (∅ : Finset (Fin h)) else {u}).card ≤ 1 := by split_ifs <;> simp
      exact (Finset.card_union_le S _).trans (Nat.add_le_add_left (hc.trans (le_max_left _ _)) _)

 theorem treewidth_transfer {h n : ℕ} (H : SimpleGraph (Fin h)) (G : SimpleGraph (Fin n))
    (E : AlmostEmbedding H G) (R : Finset (EdgeIndex H)) (U : Finset (Fin n))
    (hU : ∀ e∈R,∀ v∈E.path e,v∈U) (d : ℕ) (hd : ∀v,degree H v ≤ d) :
    PlantedSubgraphLD.tw H ≤ 2*(Finset.univ \ R).card + max 1 (2*d*(PlantedSubgraphLD.tw (induced G U)+1)) := by
  obtain ⟨T,inst,tree,bags,dec,size⟩ := treewidth_witness (induced G U)
  let := inst
  have dec' := lift_decomposition G U tree bags dec
  have size' (t : T) : ((bags t).map (numbering U)).card ≤ PlantedSubgraphLD.tw (induced G U)+1 := by
    simpa using size t
  obtain ⟨tr,bs,dec'',size''⟩ := transfer H G E R U hU tree (fun t => (bags t).map (numbering U)) dec' d _ hd size'
  apply le_trans (Nat.sInf_le (show TreewidthLE H ((deletedEndpoints H R).card+max 1 (2*d*(PlantedSubgraphLD.tw (induced G U)+1))) from
    ⟨T ⊕ Fin h,inferInstance,tr,bs,dec'',fun t => (size'' t).trans (Nat.le_succ _)⟩))
  exact Nat.add_le_add_right (deleted_card H R) _

end EdgeSublinearMWIS.Main.PartialDecomposition
end

noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.PathMass

 theorem edge_card_bound {h : ℕ} (H : SimpleGraph (Fin h)) (d : ℕ) (hd : ∀ v,degree H v ≤ d) :
    Fintype.card (EdgeIndex H) ≤ d*h := by
  let f : EdgeIndex H → Σ u : Fin h,H.neighborSet u := fun e => ⟨e.val.1,⟨e.val.2,e.property.2⟩⟩
  have hinj : Function.Injective f := by
    intro e q heq
    apply Subtype.ext
    exact congrArg (fun z : Σ u : Fin h,H.neighborSet u => (z.1,z.2.val)) heq
  calc
    _ ≤ Fintype.card (Σ u : Fin h,H.neighborSet u) := Fintype.card_le_of_injective f hinj
    _ = ∑ u : Fin h,degree H u := by rw [Fintype.card_sigma]; simp only [Set.fintypeCard_eq_ncard,degree]
    _ ≤ ∑ _u : Fin h,d := Finset.sum_le_sum (fun u _ => hd u)
    _ = _ := by simp [Nat.mul_comm]

end EdgeSublinearMWIS.Main.PathMass
end

noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.PartialDecomposition

 def incidentEdges {h : ℕ} (H : SimpleGraph (Fin h)) (x : Fin h) : Finset (EdgeIndex H) :=
  Finset.univ.filter (fun e => e.val.1=x ∨ e.val.2=x)

 theorem incidentEdges_card {h : ℕ} (H : SimpleGraph (Fin h)) (x : Fin h) :
    (incidentEdges H x).card ≤ degree H x := by
  let f : (incidentEdges H x) → H.neighborSet x := fun e =>
    if he : e.val.val.1=x then ⟨e.val.val.2,by change H.Adj x _; simpa only [he] using e.val.property.2⟩
    else ⟨e.val.val.1,by
      have hx := (Finset.mem_filter.mp e.property).2.resolve_left he
      change H.Adj x _
      simpa only [hx] using e.val.property.2.symm⟩
  have hinj : Function.Injective f := by
    intro e q heq
    have he := e.val.property.1
    have hq := q.val.property.1
    have heX := (Finset.mem_filter.mp e.property).2
    have hqX := (Finset.mem_filter.mp q.property).2
    have hh := congrArg Subtype.val heq
    dsimp [f] at hh
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> split_ifs at hh <;> rcases heX with heX | heX <;> rcases hqX with hqX | hqX <;> simp_all only [Fin.lt_def] <;> omega
  have hc := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe,Set.fintypeCard_eq_ncard,degree] using hc

 def sharingEdges {h : ℕ} (H : SimpleGraph (Fin h)) (e : EdgeIndex H) : Finset (EdgeIndex H) :=
  incidentEdges H e.val.1 ∪ incidentEdges H e.val.2

 theorem sharingEdges_card {h : ℕ} (H : SimpleGraph (Fin h)) (e : EdgeIndex H)
    (d : ℕ) (hd : ∀x,degree H x ≤ d) : (sharingEdges H e).card ≤ 2*d := by
  have h1 := (incidentEdges_card H e.val.1).trans (hd e.val.1)
  have h2 := (incidentEdges_card H e.val.2).trans (hd e.val.2)
  exact (Finset.card_union_le _ _).trans (by omega)

 def pathUnion {h n : ℕ} {H : SimpleGraph (Fin h)} {G : SimpleGraph (Fin n)}
    (E : AlmostEmbedding H G) (R : Finset (EdgeIndex H)) : Finset (Fin n) :=
  R.biUnion (fun e => (E.path e).toFinset)

 theorem mem_pathUnion {h n : ℕ} {H : SimpleGraph (Fin h)} {G : SimpleGraph (Fin n)}
    (E : AlmostEmbedding H G) (R : Finset (EdgeIndex H)) (v : Fin n) :
    v∈pathUnion E R ↔ ∃ e∈R,v∈E.path e := by simp [pathUnion]

 theorem pathUnion_card {h n : ℕ} {H : SimpleGraph (Fin h)} {G : SimpleGraph (Fin n)}
    (E : AlmostEmbedding H G) (R : Finset (EdgeIndex H)) (r : ℕ)
    (hr : ∀e∈R,(E.path e).length ≤ r) : (pathUnion E R).card ≤ R.card*r := by
  calc
    _ ≤ ∑ e∈R,(E.path e).toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _e∈R,r := Finset.sum_le_sum (fun e he => (List.toFinset_card_le _).trans (hr e he))
    _ = _ := by simp

 theorem adjacent_sharing {h n : ℕ} {H : SimpleGraph (Fin h)} {G : SimpleGraph (Fin n)}
    (E : AlmostEmbedding H G) (hE : E.Induced) (e f : EdgeIndex H)
    {u v : Fin n} (hu : u∈E.path e) (hv : v∈E.path f) (hadj : G.Adj u v) :
    f∈sharingEdges H e := by
  by_contra hh
  have hn : e.val.1 ≠ f.val.1 ∧ e.val.1 ≠ f.val.2 ∧ e.val.2 ≠ f.val.1 ∧ e.val.2 ≠ f.val.2 := by
    simp only [sharingEdges,incidentEdges,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,not_or] at hh
    exact ⟨Ne.symm hh.1.1,Ne.symm hh.1.2,Ne.symm hh.2.1,Ne.symm hh.2.2⟩
  exact hE e f hn.1 hn.2.1 hn.2.2.1 hn.2.2.2 u hu v hv hadj

 theorem induced_degree_bound {h n : ℕ} {H : SimpleGraph (Fin h)} {G : SimpleGraph (Fin n)}
    (E : AlmostEmbedding H G) (hE : E.Induced) (R : Finset (EdgeIndex H))
    (d r : ℕ) (hd : ∀x,degree H x ≤ d) (hr : ∀e∈R,(E.path e).length ≤ r)
    (i : Fin (Fintype.card (pathUnion E R))) : degree (induced G (pathUnion E R)) i ≤ 2*d*r := by
  let U := pathUnion E R
  have hiU : numbering U i ∈ U := (numbering_range U _).mpr ⟨i,rfl⟩
  obtain ⟨e,he,hie⟩ := (mem_pathUnion E R _).mp hiU
  let F := induced G U
  let S := (sharingEdges H e ∩ R).biUnion (fun f => (E.path f).toFinset)
  have hS : S.card ≤ 2*d*r := by
    calc
      _ ≤ ∑ f∈sharingEdges H e ∩ R,(E.path f).toFinset.card := Finset.card_biUnion_le
      _ ≤ ∑ _f∈sharingEdges H e ∩ R,r := Finset.sum_le_sum (fun f hf =>
        (List.toFinset_card_le _).trans (hr f (Finset.mem_inter.mp hf).2))
      _ = (sharingEdges H e ∩ R).card*r := by simp
      _ ≤ (sharingEdges H e).card*r := Nat.mul_le_mul_right _ (Finset.card_le_card Finset.inter_subset_left)
      _ ≤ (2*d)*r := Nat.mul_le_mul_right _ (sharingEdges_card H e d hd)
  let f : F.neighborSet i → S := fun j => ⟨numbering U j.val,by
    have hjU : numbering U j.val ∈ U := (numbering_range U _).mpr ⟨j.val,rfl⟩
    obtain ⟨q,hq,hjq⟩ := (mem_pathUnion E R _).mp hjU
    have hadj : G.Adj (numbering U i) (numbering U j.val) := j.property
    have hshare := adjacent_sharing E hE e q hie hjq hadj
    exact Finset.mem_biUnion.mpr ⟨q,Finset.mem_inter.mpr ⟨hshare,hq⟩,by simpa using hjq⟩⟩
  have hinj : Function.Injective f := by
    intro j k hjk
    apply Subtype.ext
    have hh : numbering U j.val = numbering U k.val := congrArg (fun z : S => z.val) hjk
    exact (numbering U).injective hh
  have hc := Fintype.card_le_of_injective f hinj
  have hc' : degree F i ≤ S.card := by simpa only [degree,Set.fintypeCard_eq_ncard,Fintype.card_coe] using hc
  exact hc'.trans hS

 theorem edgeCount_index {n : ℕ} (G : SimpleGraph (Fin n)) : edgeCount G = Fintype.card (EdgeIndex G) := by
  simp only [edgeCount,EdgeIndex,Set.ncard_eq_toFinset_card',Set.toFinset_setOf]
  exact (Fintype.card_subtype _).symm

 theorem induced_edge_bound {h n : ℕ} {H : SimpleGraph (Fin h)} {G : SimpleGraph (Fin n)}
    (E : AlmostEmbedding H G) (hE : E.Induced) (R : Finset (EdgeIndex H))
    (d r : ℕ) (hd : ∀x,degree H x ≤ d) (hr : ∀e∈R,(E.path e).length ≤ r) :
    edgeCount (induced G (pathUnion E R)) ≤ 2*d*Fintype.card (EdgeIndex H)*r^2 := by
  rw [edgeCount_index]
  have hb := PathMass.edge_card_bound _ (2*d*r) (induced_degree_bound E hE R d r hd hr)
  have hU : Fintype.card (pathUnion E R) ≤ Fintype.card (EdgeIndex H)*r := by
    simpa using (pathUnion_card E R r hr).trans (Nat.mul_le_mul_right r (Finset.card_le_univ R))
  calc
    _ ≤ 2*d*r*Fintype.card (pathUnion E R) := hb
    _ ≤ 2*d*r*(Fintype.card (EdgeIndex H)*r) := Nat.mul_le_mul_left _ hU
    _ = _ := by ring

end EdgeSublinearMWIS.Main.PartialDecomposition
end

noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.PartialDecomposition

 theorem power_obstruction (a : ℕ) (ha : 2≤a) (c K B H ell : ℝ)
    (hc : 0<c) (hK : 0<K) (hB : 0<B) (hH : 0<H) (hell : 1≤ell)
    (ineq : c*H ≤ 12*K*(B*H*ell^2)^(1-1/(a:ℝ))) :
    H ≤ ((12*K)^a*B^(a-1)/c^a)*ell^(2*a-2) := by
  have ha0 : a≠0 := by omega
  have haR : (a:ℝ)≠0 := by exact_mod_cast ha0
  have hbase : 0≤B*H*ell^2 := by positivity
  have he : (1-1/(a:ℝ))*(a:ℝ)=((a-1:ℕ):ℝ) := by
    rw [Nat.cast_sub (by omega : 1≤a),Nat.cast_one]
    field_simp
  have hp := pow_le_pow_left₀ (by positivity : 0≤c*H) ineq a
  rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hbase, he,Real.rpow_natCast,
    mul_pow,mul_pow,mul_pow] at hp
  have hHa : H^a = H^(a-1)*H := by rw [← pow_succ]; congr 1; omega
  have hellpow : (ell^2)^(a-1)=ell^(2*a-2) := by rw [← pow_mul]; congr 1; omega
  rw [hHa,hellpow] at hp
  have hp' : H^(a-1)*(c^a*H) ≤ H^(a-1)*((12*K)^a*B^(a-1)*ell^(2*a-2)) := by
    simp only [mul_pow]
    nlinarith only [hp]
  have hp'' := (mul_le_mul_iff_right₀ (pow_pos hH (a-1))).mp hp'
  apply (mul_le_mul_iff_left₀ (pow_pos hc a)).mp
  calc
    H*c^a = c^a*H := mul_comm _ _
    _ ≤ (12*K)^a*B^(a-1)*ell^(2*a-2) := hp''
    _ = (((12*K)^a*B^(a-1)/c^a)*ell^(2*a-2))*c^a := by field_simp [hc.ne']

end EdgeSublinearMWIS.Main.PartialDecomposition
end

noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.PartialDecomposition

 theorem short_model {h n : ℕ} (H : SimpleGraph (Fin h)) (G : SimpleGraph (Fin n))
    (E : AlmostEmbedding H G) (hE : E.Induced) (c ell A : ℝ)
    (hc : 0<c) (hell : 1≤ell) (hA : 1≤A) (hcA : 96≤c*A)
    (hd : ∀v,degree H v ≤ 3) (htw : c*h ≤ (PlantedSubgraphLD.tw H:ℝ))
    (hh : 24≤c*h)
    (htotal : (∑ e : EdgeIndex H,((E.path e).length:ℝ)) ≤ 4*ell*Fintype.card (EdgeIndex H)) :
    ∃ U : Finset (Fin n), c*h ≤ 12*(PlantedSubgraphLD.tw (induced G U):ℝ) ∧
      (edgeCount (induced G U):ℝ) ≤ (18*(A+1)^2)*(h:ℝ)*ell^2 := by
  let r := Nat.ceil (A*ell)
  let R := Finset.univ.filter (fun e : EdgeIndex H => (E.path e).length ≤ r)
  let D := Finset.univ \ R
  let U := pathUnion E R
  have hlen : ∀e∈R,(E.path e).length ≤ r := fun e he => (Finset.mem_filter.mp he).2
  have hU : ∀e∈R,∀v∈E.path e,v∈U := fun e he v hv => (mem_pathUnion E R v).mpr ⟨e,he,hv⟩
  have hEdge : (Fintype.card (EdgeIndex H):ℝ) ≤ 3*h := by exact_mod_cast PathMass.edge_card_bound H 3 hd
  have hellpos : 0<ell := by linarith
  have hAell : 0≤A*ell := by positivity
  have hrlo : A*ell ≤ (r:ℝ) := Nat.le_ceil _
  have hrhi : (r:ℝ) ≤ (A+1)*ell := by
    have hh := (Nat.ceil_lt_add_one hAell).le
    dsimp only [r]
    nlinarith
  have hDlen : (r:ℝ)*D.card ≤ ∑ e∈D,((E.path e).length:ℝ) := by
    calc
      _ = ∑ _e∈D,(r:ℝ) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun e he => by
        have hn : ¬(E.path e).length ≤ r := by simpa [D,R] using (Finset.mem_sdiff.mp he).2
        exact_mod_cast (by omega : r≤(E.path e).length))
  have hDsum : (∑ e∈D,((E.path e).length:ℝ)) ≤ ∑ e : EdgeIndex H,((E.path e).length:ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.cast_nonneg _)
  have hDmult : A*ell*D.card ≤ 12*ell*h := by
    calc
      _ ≤ (r:ℝ)*D.card := mul_le_mul_of_nonneg_right hrlo (Nat.cast_nonneg _)
      _ ≤ ∑ e∈D,((E.path e).length:ℝ) := hDlen
      _ ≤ ∑ e : EdgeIndex H,((E.path e).length:ℝ) := hDsum
      _ ≤ 4*ell*Fintype.card (EdgeIndex H) := htotal
      _ ≤ 12*ell*h := by nlinarith
  have hD : A*(D.card:ℝ) ≤ 12*h := by
    apply (mul_le_mul_iff_right₀ hellpos).mp
    nlinarith [hDmult]
  have hDsmall : 8*(D.card:ℝ) ≤ c*h := by
    have hmul := mul_le_mul_of_nonneg_left hD hc.le
    have hmul' := mul_le_mul_of_nonneg_right hcA (Nat.cast_nonneg D.card)
    nlinarith
  have ht := treewidth_transfer H G E R U hU 3 hd
  have hmax : max 1 (2*3*(PlantedSubgraphLD.tw (induced G U)+1)) = 6*(PlantedSubgraphLD.tw (induced G U)+1) := by omega
  rw [hmax] at ht
  have htR : (PlantedSubgraphLD.tw H:ℝ) ≤ 2*(D.card:ℝ)+6*((PlantedSubgraphLD.tw (induced G U):ℝ)+1) := by exact_mod_cast ht
  refine ⟨U,by nlinarith,?_⟩
  have hm := induced_edge_bound E hE R 3 r hd hlen
  have hmR : (edgeCount (induced G U):ℝ) ≤ 6*(Fintype.card (EdgeIndex H):ℝ)*(r:ℝ)^2 := by exact_mod_cast hm
  calc
    _ ≤ 6*(Fintype.card (EdgeIndex H):ℝ)*(r:ℝ)^2 := hmR
    _ ≤ 18*(h:ℝ)*(r:ℝ)^2 := by nlinarith [sq_nonneg (r:ℝ)]
    _ ≤ 18*(h:ℝ)*((A+1)*ell)^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hrhi 2) (by positivity)
    _ = _ := by ring

end EdgeSublinearMWIS.Main.PartialDecomposition
end

noncomputable section

open scoped BigOperators Classical
open EdgeSublinearMWIS.Main
open EdgeSublinearMWIS.Main.PartialDecomposition
set_option autoImplicit false

theorem solution (C : GraphClass) (a : ℕ) (K : ℝ)
    (hereditary : Hereditary C) (ha : 2 ≤ a) (bound : TreewidthBound C a K) :
    ∃ D : ℝ, 0 < D ∧ ∀ ell : ℝ, 1 ≤ ell →
      ∃ (h : ℕ) (H : SimpleGraph (Fin h)), 0 < Fintype.card (EdgeIndex H) ∧
        (h : ℝ) ≤ D * ell ^ (2*a-2) ∧ (∀ v,degree H v ≤ 3) ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
        ∀ E : AlmostEmbedding H G,E.Induced →
          4*ell*Fintype.card (EdgeIndex H) < ∑ e : EdgeIndex H,((E.path e).length:ℝ) := by
  have hK : 0<K := bound.1
  obtain ⟨c,t0,hc,hfam⟩ := lemma_10
  let A := max 1 (96/c)
  let B := 18*(A+1)^2
  let Q := (12*K)^a*B^(a-1)/c^a
  let F := max 1 (max (t0:ℝ) (24/c)) + Q + 1
  have hA : 1≤A := le_max_left _ _
  have hApos : 0<A := by linarith
  have hcA : 96≤c*A := by
    have hh := mul_le_mul_of_nonneg_left (le_max_right 1 (96/c)) hc.le
    dsimp only [A]
    field_simp at hh
    nlinarith
  have hB : 0<B := by dsimp [B]; positivity
  have hQ : 0<Q := by dsimp [Q]; positivity
  have hF : 0<F := by dsimp [F]; have hh := le_max_left 1 (max (t0:ℝ) (24/c)); linarith
  have hF1 : 1≤F := by dsimp [F]; have hh := le_max_left 1 (max (t0:ℝ) (24/c)); linarith
  refine ⟨F+1,by linarith,?_⟩
  intro ell hell
  have hellpos : 0<ell := by linarith
  have hpow : 1≤ell^(2*a-2) := one_le_pow₀ hell
  let h := Nat.ceil (F*ell^(2*a-2))
  have hlo : F*ell^(2*a-2) ≤ (h:ℝ) := Nat.le_ceil _
  have hhi : (h:ℝ) ≤ (F+1)*ell^(2*a-2) := by
    have hh := (Nat.ceil_lt_add_one (show 0≤F*ell^(2*a-2) by positivity)).le
    dsimp only [h]
    nlinarith
  have hFlo : F ≤ (h:ℝ) := by nlinarith
  have hhpos : 0<(h:ℝ) := by linarith
  have ht0 : t0≤h := by
    have h1 := le_max_left (t0:ℝ) (24/c)
    have h2 := le_max_right 1 (max (t0:ℝ) (24/c))
    have hf : (t0:ℝ) ≤ F := by dsimp [F]; linarith
    exact_mod_cast (hf.trans hFlo)
  have hch : 24≤c*h := by
    have h1 := le_max_right (t0:ℝ) (24/c)
    have h2 := le_max_right 1 (max (t0:ℝ) (24/c))
    have hf : 24/c≤F := by dsimp [F]; linarith
    have hh := mul_le_mul_of_nonneg_left (hf.trans hFlo) hc.le
    simpa only [mul_div_cancel₀ _ hc.ne'] using hh
  obtain ⟨H,hd,htw⟩ := hfam h ht0
  have hedge : 0<Fintype.card (EdgeIndex H) := by
    by_contra hn
    have hz : Fintype.card (EdgeIndex H)=0 := by omega
    have hzero : edgeCount H=0 := by rw [edgeCount_index,hz]
    have htwzero := BlowupDecomposition.treewidth_zero H hzero
    rw [htwzero,Nat.cast_zero] at htw
    nlinarith
  refine ⟨h,H,hedge,hhi,hd,?_⟩
  intro n G hC E hE
  by_contra hnot
  have htotal : (∑ e : EdgeIndex H,((E.path e).length:ℝ)) ≤ 4*ell*Fintype.card (EdgeIndex H) := le_of_not_gt hnot
  obtain ⟨U,ht,hm⟩ := short_model H G E hE c ell A hc hell hA hcA hd htw hch htotal
  have hclass := induced_mem C hereditary G U hC
  have hb := bound.2 _ (induced G U) hclass
  have haR : 1≤(a:ℝ) := by exact_mod_cast (by omega : 1≤a)
  have hbeta : 0≤1-1/(a:ℝ) := by have := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) haR; simp only [one_div] at *; norm_num at this; linarith
  have hmono := Real.rpow_le_rpow (Nat.cast_nonneg (edgeCount (induced G U))) hm hbeta
  have hfinal : c*(h:ℝ) ≤ 12*K*(B*(h:ℝ)*ell^2)^(1-1/(a:ℝ)) := by
    dsimp only [B] at hmono ⊢
    nlinarith [mul_le_mul_of_nonneg_left hmono bound.1.le]
  have hbound := power_obstruction a ha c K B h ell hc bound.1 hB hhpos hell hfinal
  change (h:ℝ) ≤ Q*ell^(2*a-2) at hbound
  have hFQ : Q+1≤F := by dsimp [F]; have hh := le_max_left 1 (max (t0:ℝ) (24/c)); linarith
  have hstrict := mul_le_mul_of_nonneg_right hFQ (pow_nonneg hellpos.le (2*a-2))
  nlinarith
end
