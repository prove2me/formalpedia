-- Prove2me | solution 1 for GavrilSubtree.Chordal.hasCliqueTree_of_isChordal
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T00:27:52.770747+00:00
-- url     : https://prove2.me/submissions/1f0d1cfa-363d-4a0a-8a23-97f5e9f75746

import Mathlib
import Definitions.Def_GavrilSubtree_Chordal_Setting

universe u

namespace CliqueTreeAux

open SimpleGraph

section Leaf

variable {β : Type u}

/-- The tree `T` with one new leaf `none` attached to `K`. -/
def leaf (T : SimpleGraph β) (K : β) : SimpleGraph (Option β) :=
  T.map Function.Embedding.some ⊔ SimpleGraph.edge none (some K)

lemma leaf_adj_some_some (T : SimpleGraph β) (K a b : β) :
    (leaf T K).Adj (some a) (some b) ↔ T.Adj a b := by
  rw [leaf, sup_adj, SimpleGraph.map_adj]
  simp [SimpleGraph.edge_adj]

lemma leaf_adj_none (T : SimpleGraph β) (K b : β) :
    (leaf T K).Adj none (some b) ↔ b = K := by
  rw [leaf, sup_adj, SimpleGraph.map_adj]
  simp [SimpleGraph.edge_adj, eq_comm]

def leafHom (T : SimpleGraph β) (K : β) : T →g leaf T K :=
  ⟨some, fun h => (leaf_adj_some_some T K _ _).2 h⟩

lemma leaf_reach {T : SimpleGraph β} (hT : T.Connected) (K : β) (o : Option β) :
    (leaf T K).Reachable (some K) o := by
  cases o with
  | none => exact Adj.reachable ((leaf_adj_none T K K).2 rfl).symm
  | some b => exact (hT.preconnected K b).map (leafHom T K)

lemma leaf_connected {T : SimpleGraph β} (hT : T.Connected) (K : β) : (leaf T K).Connected := by
  have : Nonempty (Option β) := ⟨none⟩
  exact ⟨fun x y => (leaf_reach hT K x).symm.trans (leaf_reach hT K y)⟩

lemma leaf_isTree [Finite β] {T : SimpleGraph β} (hT : T.IsTree) (K : β) :
    (leaf T K).IsTree := by
  have hT' := isTree_iff_connected_and_card.1 hT
  rw [isTree_iff_connected_and_card]
  refine ⟨leaf_connected hT.connected K, ?_⟩
  have h1 : (leaf T K).edgeSet =
      (Function.Embedding.some (α := β)).sym2Map '' T.edgeSet ∪ {s(none, some K)} := by
    rw [leaf, edgeSet_sup, edgeSet_map, edgeSet_edge_of_ne (by simp)]
  have h2 : Disjoint ((Function.Embedding.some (α := β)).sym2Map '' T.edgeSet)
      {s(none, some K)} := by
    rw [Set.disjoint_singleton_right]
    rintro ⟨e, _, h⟩
    induction e using Sym2.ind with
    | _ a b => simp [Function.Embedding.sym2Map_apply] at h
  have h3 : (leaf T K).edgeSet.ncard = T.edgeSet.ncard + 1 := by
    rw [h1, Set.ncard_union_eq h2 (Set.toFinite _) (Set.toFinite _),
      Set.ncard_image_of_injective _ (Function.Embedding.injective _),
      Set.ncard_singleton]
  have h4 : Nat.card (Option β) = Nat.card β + 1 := by
    have := Fintype.ofFinite β
    simp [Nat.card_eq_fintype_card]
  rw [Nat.card_coe_set_eq, h3, h4, ← hT'.2, Nat.card_coe_set_eq]

lemma leaf_conn_image {T : SimpleGraph β} {K : β} {X : Set β} (hX : (T.induce X).Connected) :
    ((leaf T K).induce (Option.some '' X)).Connected := by
  refine hX.map ⟨fun x => ⟨some x.1, x.1, x.2, rfl⟩, fun h => (leaf_adj_some_some T K _ _).2 h⟩ ?_
  rintro ⟨_, b, hb, rfl⟩
  exact ⟨⟨b, hb⟩, rfl⟩

lemma leaf_conn_insert {T : SimpleGraph β} {K : β} {X : Set β} (hX : (T.induce X).Connected)
    (hK : K ∈ X) : ((leaf T K).induce (insert none (Option.some '' X))).Connected := by
  let f : (T.induce X) →g ((leaf T K).induce (insert none (Option.some '' X))) :=
    ⟨fun x => ⟨some x.1, Or.inr ⟨x.1, x.2, rfl⟩⟩, fun h => (leaf_adj_some_some T K _ _).2 h⟩
  have key : ∀ y : (insert none (Option.some '' X) : Set (Option β)),
      ((leaf T K).induce (insert none (Option.some '' X))).Reachable
        ⟨some K, Or.inr ⟨K, hK, rfl⟩⟩ y := by
    rintro ⟨o, ho⟩
    rcases ho with rfl | ⟨b, hb, rfl⟩
    · exact Adj.reachable (show (leaf T K).Adj (some K) none from
        ((leaf_adj_none T K K).2 rfl).symm)
    · exact (hX.preconnected ⟨K, hK⟩ ⟨b, hb⟩).map f
  have : Nonempty (insert none (Option.some '' X) : Set (Option β)) := ⟨⟨none, Or.inl rfl⟩⟩
  exact ⟨fun a b => (key a).symm.trans (key b)⟩

lemma conn_singleton (T : SimpleGraph β) (X : Set β) (a : β) (h : X = {a}) :
    (T.induce X).Connected := by
  subst h
  have : Nonempty ({a} : Set β) := ⟨⟨a, rfl⟩⟩
  refine ⟨fun x y => ?_⟩
  have : x = y := Subtype.ext (by rw [x.2, y.2])
  rw [this]

end Leaf

section Dirac

variable {V : Type u} {G : SimpleGraph V}

lemma two_le_length {u w : V} (b : G.Walk u w) (h : G.Adj u w) (he : s(u, w) ∉ b.edges) :
    2 ≤ b.length := by
  cases b with
  | nil => exact absurd rfl h.ne
  | cons h' b' =>
    cases b' with
    | nil => simp at he
    | cons h'' b'' => simp

lemma shortcut {s t x y : V} (p : G.Walk s t) (hx : x ∈ p.support) (hy : y ∈ p.support)
    (hxy : G.Adj x y) (he : s(x, y) ∉ p.edges) :
    ∃ p' : G.Walk s t, p'.length < p.length ∧ ∀ z ∈ p'.support, z ∈ p.support := by
  obtain ⟨a1, a2, rfl⟩ := p.mem_support_iff_exists_append.mp hx
  rw [Walk.mem_support_append_iff] at hy
  rcases hy with hy | hy
  · obtain ⟨b, r, rfl⟩ := a1.mem_support_iff_exists_append.mp hy
    have h2 := two_le_length r hxy.symm (by
      intro h; apply he; simp [Walk.edges_append, Sym2.eq_swap] at h ⊢; tauto)
    refine ⟨b.append (Walk.cons hxy.symm a2), ?_, ?_⟩
    · simp [Walk.length_append]; omega
    · intro z hz
      simp only [Walk.mem_support_append_iff, Walk.support_cons, List.mem_cons] at hz ⊢
      have := r.start_mem_support
      rcases hz with hz | rfl | hz <;> tauto
  · obtain ⟨b, r, rfl⟩ := a2.mem_support_iff_exists_append.mp hy
    have h2 := two_le_length b hxy (by
      intro h; apply he; simp [Walk.edges_append] at h ⊢; tauto)
    refine ⟨a1.append (Walk.cons hxy r), ?_, ?_⟩
    · simp [Walk.length_append]; omega
    · intro z hz
      simp only [Walk.mem_support_append_iff, Walk.support_cons, List.mem_cons] at hz ⊢
      have := b.start_mem_support
      rcases hz with hz | rfl | hz <;> tauto

lemma clique_of_path (hG : GavrilSubtree.Chordal.IsChordal G) (v : V) (K : Set V)
    (hK : ∀ x ∈ K, x ≠ v ∧ ¬ G.Adj v x) :
    ∀ (n : ℕ) (s t : V) (p : G.Walk s t), p.length = n → p.IsPath → s ≠ t → G.Adj v s →
      G.Adj v t → (∀ y ∈ p.support, y = s ∨ y = t ∨ y ∈ K) → G.Adj s t := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s t p hn hp hst hs ht hsupp
  classical
  by_cases h1 : p.length = 1
  · exact Walk.adj_of_length_eq_one h1
  have h0 : p.length ≠ 0 := fun h => hst (Walk.eq_of_length_eq_zero h)
  have hvp : v ∉ p.support := by
    intro hv
    rcases hsupp v hv with h | h | h
    · exact hs.ne h
    · exact ht.ne h
    · exact (hK v h).1 rfl
  set c : G.Walk s s := Walk.cons hs.symm (Walk.cons ht p.reverse) with hc
  have hcyc : c.IsCycle := by
    rw [hc, Walk.cons_isCycle_iff, Walk.cons_isPath_iff]
    refine ⟨⟨hp.reverse, by simpa using hvp⟩, ?_⟩
    simp only [Walk.edges_cons, Walk.edges_reverse, List.mem_cons, List.mem_reverse, not_or]
    refine ⟨?_, ?_⟩
    · intro h
      rw [Sym2.eq_iff] at h
      rcases h with ⟨h1, h2⟩ | ⟨h, _⟩
      · exact hst (h1.trans h2)
      · exact hst h
    · intro h
      exact hvp (p.snd_mem_support_of_mem_edges h)
  have hlen : 4 ≤ c.length := by
    simp [hc]; omega
  obtain ⟨x, hx, y, hy, hxy, hne⟩ := hG s c hcyc hlen
  have hcs : ∀ z ∈ c.support, z = v ∨ z ∈ p.support := by
    intro z hz
    simp only [hc, Walk.support_cons, Walk.support_reverse, List.mem_cons, List.mem_reverse] at hz
    rcases hz with h | h | h
    · right; rw [h]; exact p.start_mem_support
    · left; exact h
    · right; exact h
  have hedges : ∀ e ∈ p.edges, e ∈ c.edges := by
    intro e he
    simp [hc, he]
  have hv : ∀ y ∈ p.support, G.Adj v y → s(v, y) ∈ c.edges := by
    intro y hy hvy
    rcases hsupp y hy with h | h | h
    · subst h; simp [hc, Sym2.eq_swap]
    · subst h; simp [hc]
    · exact absurd hvy (hK y h).2
  rcases hcs x hx with rfl | hxp
  · rcases hcs y hy with rfl | hyp
    · exact absurd hxy (G.loopless.irrefl _)
    · exact absurd (hv y hyp hxy) hne
  rcases hcs y hy with rfl | hyp
  · exact absurd (by rw [Sym2.eq_swap]; exact hv x hxp hxy.symm) hne
  have hne' : s(x, y) ∉ p.edges := fun h => hne (hedges _ h)
  obtain ⟨p', hlt, hsub⟩ := shortcut p hxp hyp hxy hne'
  have hb := p'.bypass_isPath
  exact ih p'.bypass.length (lt_of_le_of_lt p'.length_bypass_le_length (hn ▸ hlt)) s t _ rfl hb
    hst hs ht (fun z hz => hsupp z (hsub z (p'.support_bypass_subset_support hz)))

/-- `a` is simplicial inside the vertex set `A`. -/
def Simp (G : SimpleGraph V) (A : Finset V) (a : V) : Prop :=
  ∀ y ∈ A, ∀ z ∈ A, G.Adj a y → G.Adj a z → y ≠ z → G.Adj y z

lemma dirac_aux (hG : GavrilSubtree.Chordal.IsChordal G) : ∀ (n : ℕ) (A : Finset V),
    A.card = n → (∀ x ∈ A, ∀ y ∈ A, x ≠ y → G.Adj x y) ∨
    ∃ a ∈ A, ∃ b ∈ A, ¬ G.Adj a b ∧ a ≠ b ∧ Simp G A a ∧ Simp G A b := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hn
  by_cases hcl : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → G.Adj x y
  · exact Or.inl hcl
  right
  push Not at hcl
  obtain ⟨v, hv, u, hu, hvu, hnadj⟩ := hcl
  obtain ⟨K, hKdef⟩ : ∃ K : Set V, ∀ x, x ∈ K ↔ x ∈ A ∧ x ≠ v ∧ ¬ G.Adj v x :=
    ⟨{x | x ∈ A ∧ x ≠ v ∧ ¬ G.Adj v x}, fun x => Iff.rfl⟩
  have hKv : ∀ x ∈ K, x ≠ v ∧ ¬ G.Adj v x := fun x hx => ((hKdef x).1 hx).2
  have hKA : ∀ x ∈ K, x ∈ A := fun x hx => ((hKdef x).1 hx).1
  have huK : u ∈ K := (hKdef u).2 ⟨hu, hvu.symm, hnadj⟩
  obtain ⟨C, hCdef⟩ : ∃ C : Finset V, ∀ x, x ∈ C ↔
      x ∈ A ∧ ∃ p : G.Walk u x, ∀ y ∈ p.support, y ∈ K :=
    ⟨A.filter (fun x => ∃ p : G.Walk u x, ∀ y ∈ p.support, y ∈ K), by simp⟩
  have huC : u ∈ C := (hCdef u).2 ⟨hu, Walk.nil, by simpa using huK⟩
  have hCK : ∀ x ∈ C, x ∈ K := by
    intro x hx
    obtain ⟨_, p, hp⟩ := (hCdef x).1 hx
    exact hp x p.end_mem_support
  have hCA : ∀ x ∈ C, x ∈ A := fun x hx => ((hCdef x).1 hx).1
  have hCext : ∀ x ∈ C, ∀ y ∈ K, G.Adj x y → y ∈ C := by
    intro x hx y hy hxy
    obtain ⟨_, p, hp⟩ := (hCdef x).1 hx
    refine (hCdef y).2 ⟨hKA y hy, p.concat hxy, ?_⟩
    intro z hz
    simp only [Walk.support_concat, List.mem_append,
      List.mem_singleton] at hz
    rcases hz with hz | rfl
    · exact hp z hz
    · exact hy
  obtain ⟨NC, hNCdef⟩ : ∃ NC : Finset V, ∀ x, x ∈ NC ↔
      x ∈ A ∧ x ∉ C ∧ ∃ c ∈ C, G.Adj c x :=
    ⟨A.filter (fun x => x ∉ C ∧ ∃ c ∈ C, G.Adj c x), by simp⟩
  have hNCv : ∀ x ∈ NC, G.Adj v x := by
    intro x hx
    obtain ⟨hxA, hxC, c, hc, hcx⟩ := (hNCdef x).1 hx
    by_contra hvx
    have hxv : x ≠ v := by
      rintro rfl
      exact (hKv c (hCK c hc)).2 hcx.symm
    exact hxC (hCext c hc x ((hKdef x).2 ⟨hxA, hxv, hvx⟩) hcx)
  have hnbr : ∀ c ∈ C, ∀ y ∈ A, G.Adj c y → y ∈ C ∨ y ∈ NC := by
    intro c hc y hy hcy
    by_cases hyC : y ∈ C
    · exact Or.inl hyC
    · exact Or.inr ((hNCdef y).2 ⟨hy, hyC, c, hc, hcy⟩)
  have hNCclique : ∀ s ∈ NC, ∀ t ∈ NC, s ≠ t → G.Adj s t := by
    intro s hs t ht hst
    obtain ⟨hsA, hsC, c1, hc1, hc1s⟩ := (hNCdef s).1 hs
    obtain ⟨htA, htC, c2, hc2, hc2t⟩ := (hNCdef t).1 ht
    obtain ⟨_, w1, hw1⟩ := (hCdef c1).1 hc1
    obtain ⟨_, w2, hw2⟩ := (hCdef c2).1 hc2
    let P : G.Walk s t := Walk.cons hc1s.symm ((w1.reverse.append w2).concat hc2t)
    have hP : ∀ y ∈ P.support, y = s ∨ y = t ∨ y ∈ K := by
      intro y hy
      simp only [P, Walk.support_cons, Walk.support_concat, Walk.support_append,
        Walk.support_reverse, List.concat_eq_append, List.mem_cons, List.mem_append,
        List.mem_reverse, List.mem_singleton] at hy
      rcases hy with h | (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (hw1 y h))
      · exact Or.inr (Or.inr (hw2 y (List.mem_of_mem_tail h)))
      · exact Or.inr (Or.inl (by simpa using h))
    have := clique_of_path hG v K hKv _ s t P.bypass rfl P.bypass_isPath hst (hNCv s hs)
      (hNCv t ht) (fun y hy => hP y (P.support_bypass_subset_support hy))
    exact this
  have hSimpC : ∀ a ∈ C, Simp G (C ∪ NC) a → Simp G A a := by
    intro a ha hs y hy z hz hay haz hyz
    rcases hnbr a ha y hy hay with h1 | h1 <;> rcases hnbr a ha z hz haz with h2 | h2 <;>
      exact hs y (by simp [h1]) z (by simp [h2]) hay haz hyz
  have hCNCsub : C ∪ NC ⊆ A := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact hCA x h
    · exact ((hNCdef x).1 h).1
  have hvC : v ∉ C := fun h => (hKv v (hCK v h)).1 rfl
  have hvNC : v ∉ NC := fun h => G.loopless.irrefl _ (hNCv v h)
  have h1 : (C ∪ NC).card < n := by
    rw [← hn]
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hCNCsub).2 ⟨v, hv, ?_⟩)
    simp [hvC, hvNC]
  have h2 : (A \ C).card < n := by
    rw [← hn]
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset Finset.sdiff_subset).2
      ⟨u, hu, ?_⟩)
    simp [huC]
  -- a simplicial vertex in `C`
  obtain ⟨a, haC, haS⟩ : ∃ a ∈ C, Simp G A a := by
    rcases ih _ h1 (C ∪ NC) rfl with hcl1 | ⟨a1, ha1, b1, hb1, hnab, hne, hs1, hs2⟩
    · refine ⟨u, huC, hSimpC u huC ?_⟩
      intro y hy z hz _ _ hyz
      exact hcl1 y hy z hz hyz
    · by_cases h : a1 ∈ C
      · exact ⟨a1, h, hSimpC a1 h hs1⟩
      · by_cases h' : b1 ∈ C
        · exact ⟨b1, h', hSimpC b1 h' hs2⟩
        · exfalso
          have hx : a1 ∈ NC := by
            rcases Finset.mem_union.1 ha1 with h'' | h''
            · exact absurd h'' h
            · exact h''
          have hy : b1 ∈ NC := by
            rcases Finset.mem_union.1 hb1 with h'' | h''
            · exact absurd h'' h'
            · exact h''
          exact hnab (hNCclique a1 hx b1 hy hne)
  -- a simplicial vertex outside `C ∪ NC`
  have hSimpB : ∀ b ∈ A \ C, b ∉ NC → Simp G (A \ C) b → Simp G A b := by
    intro b hb hbNC hs y hy z hz hby hbz hyz
    have hbA : b ∈ A := (Finset.mem_sdiff.1 hb).1
    have hbC : b ∉ C := (Finset.mem_sdiff.1 hb).2
    have hyC : y ∉ C := fun h => hbNC ((hNCdef b).2 ⟨hbA, hbC, y, h, hby.symm⟩)
    have hzC : z ∉ C := fun h => hbNC ((hNCdef b).2 ⟨hbA, hbC, z, h, hbz.symm⟩)
    exact hs y (Finset.mem_sdiff.2 ⟨hy, hyC⟩) z (Finset.mem_sdiff.2 ⟨hz, hzC⟩) hby hbz hyz
  obtain ⟨b, hbB, hbNC, hbS⟩ : ∃ b ∈ A \ C, b ∉ NC ∧ Simp G A b := by
    rcases ih _ h2 (A \ C) rfl with hcl2 | ⟨a2, ha2, b2, hb2, hnab, hne, hs1, hs2⟩
    · refine ⟨v, Finset.mem_sdiff.2 ⟨hv, hvC⟩, hvNC, ?_⟩
      intro y hy z hz hvy hvz hyz
      have hyC : y ∉ C := fun h => (hKv y (hCK y h)).2 hvy
      have hzC : z ∉ C := fun h => (hKv z (hCK z h)).2 hvz
      exact hcl2 y (Finset.mem_sdiff.2 ⟨hy, hyC⟩) z (Finset.mem_sdiff.2 ⟨hz, hzC⟩) hyz
    · by_cases h : a2 ∈ NC
      · by_cases h' : b2 ∈ NC
        · exact absurd (hNCclique a2 h b2 h' hne) hnab
        · exact ⟨b2, hb2, h', hSimpB b2 hb2 h' hs2⟩
      · exact ⟨a2, ha2, h, hSimpB a2 ha2 h hs1⟩
  have hbA : b ∈ A := (Finset.mem_sdiff.1 hbB).1
  have hbC : b ∉ C := (Finset.mem_sdiff.1 hbB).2
  refine ⟨a, hCA a haC, b, hbA, ?_, ?_, haS, hbS⟩
  · intro h
    exact hbNC ((hNCdef b).2 ⟨hbA, hbC, a, haC, h⟩)
  · rintro rfl
    exact hbC haC


lemma exists_simp {V : Type u} {G : SimpleGraph V} (hG : GavrilSubtree.Chordal.IsChordal G)
    (A : Finset V) (hA : A.Nonempty) : ∃ v ∈ A, Simp G A v := by
  rcases dirac_aux hG _ A rfl with h | ⟨a, ha, _, _, _, _, hsa, _⟩
  · obtain ⟨v, hv⟩ := hA
    exact ⟨v, hv, fun y hy z hz _ _ hyz => h y hy z hz hyz⟩
  · exact ⟨a, ha, hsa⟩

end Dirac

section Main

open Classical

variable {V : Type u} [Finite V] (G : SimpleGraph V)

/-- cliques of `G` inside `A` -/
def Cl (A : Finset V) (s : Set V) : Prop := s ⊆ (A : Set V) ∧ G.IsClique s

/-- `(β, T, c)` is a clique tree of the induced graph `G[A]`. -/
def Good (A : Finset V) (β : Type u) (T : SimpleGraph β) (c : β → Set V) : Prop :=
  T.IsTree ∧ Function.Injective c ∧ (∀ s, s ∈ Set.range c ↔ Maximal (Cl G A) s) ∧
    ∀ w ∈ A, (T.induce {b | w ∈ c b}).Connected

/-- neighbours of `v` inside `A` -/
def Nb (A : Finset V) (v : V) : Set V := {x | x ∈ A ∧ G.Adj v x}

variable {G} {A : Finset V} {v : V}

lemma Nb_sub {x : V} (hx : x ∈ Nb G A v) : x ∈ A.erase v :=
  Finset.mem_erase.2 ⟨(G.ne_of_adj hx.2).symm, hx.1⟩

lemma Nb_clique (hs : Simp G A v) : G.IsClique (Nb G A v) :=
  fun _ hy _ hz hyz => hs _ hy.1 _ hz.1 hy.2 hz.2 hyz

lemma cl_Nb (hs : Simp G A v) : Cl G (A.erase v) (Nb G A v) :=
  ⟨fun _ hx => Nb_sub hx, Nb_clique hs⟩

lemma v_notMem_Nb : v ∉ Nb G A v := fun h => G.loopless.irrefl _ h.2

lemma cl_insert (hv : v ∈ A) (hs : Simp G A v) : Cl G A (insert v (Nb G A v)) := by
  refine ⟨?_, (Nb_clique hs).insert ?_⟩
  · intro x hx
    rcases hx with rfl | hx
    · exact hv
    · exact hx.1
  · intro b hb _
    exact hb.2

lemma cl_sub_insert (hv : v ∈ A) {s : Set V} (h : Cl G A s) (hvs : v ∈ s) :
    s ⊆ insert v (Nb G A v) := by
  intro x hx
  by_cases hxv : x = v
  · exact Or.inl hxv
  · exact Or.inr ⟨h.1 hx, h.2 hvs hx (Ne.symm hxv)⟩

lemma cl_erase {s : Set V} (h : Cl G A s) (hvs : v ∉ s) : Cl G (A.erase v) s := by
  refine ⟨fun x hx => ?_, h.2⟩
  have : x ≠ v := fun hxv => hvs (hxv ▸ hx)
  exact Finset.mem_erase.2 ⟨this, h.1 hx⟩

lemma cl_of_erase {s : Set V} (h : Cl G (A.erase v) s) : Cl G A s :=
  ⟨fun x hx => Finset.mem_of_mem_erase (h.1 hx), h.2⟩

lemma max_iff (hv : v ∈ A) (hs : Simp G A v) (s : Set V) :
    Maximal (Cl G A) s ↔
      (Maximal (Cl G (A.erase v)) s ∧ s ≠ Nb G A v) ∨ s = insert v (Nb G A v) := by
  constructor
  · intro hm
    by_cases hvs : v ∈ s
    · right
      have h1 := cl_sub_insert hv hm.1 hvs
      exact Set.Subset.antisymm h1 (hm.2 (cl_insert hv hs) h1)
    · left
      refine ⟨⟨cl_erase hm.1 hvs, fun t ht hst => hm.2 (cl_of_erase ht) hst⟩, ?_⟩
      intro hsN
      have := hm.2 (cl_insert hv hs) (hsN ▸ Set.subset_insert _ _)
      exact hvs (this (Set.mem_insert _ _))
  · rintro (⟨⟨hc, hm⟩, hne⟩ | rfl)
    · refine ⟨cl_of_erase hc, fun t ht hst => ?_⟩
      by_cases hvt : v ∈ t
      · exfalso
        have h1 := cl_sub_insert hv ht hvt
        have hvs : v ∉ s := fun h => by simpa using hc.1 h
        have hsN : s ⊆ Nb G A v := fun x hx => by
          rcases h1 (hst hx) with rfl | h
          · exact absurd hx hvs
          · exact h
        exact hne (Set.Subset.antisymm hsN (hm (cl_Nb hs) hsN))
      · exact hm (cl_erase ht hvt) hst
    · exact ⟨cl_insert hv hs, fun t ht hst => cl_sub_insert hv ht (hst (Set.mem_insert _ _))⟩

lemma exists_max_above {A : Finset V} {N : Set V} (h : Cl G A N) :
    ∃ K, N ⊆ K ∧ Maximal (Cl G A) K := by
  have hfin : {t | Cl G A t}.Finite := (A.finite_toSet.finite_subsets).subset (fun t ht => ht.1)
  obtain ⟨K, hK, hmax⟩ := Set.Finite.exists_le_maximal hfin h
  exact ⟨K, hK, hmax⟩

lemma step (hv : v ∈ A) (hs : Simp G A v) {β : Type u} {T : SimpleGraph β} {c : β → Set V}
    (h : Good G (A.erase v) β T c) :
    ∃ (β' : Type u) (T' : SimpleGraph β') (c' : β' → Set V), Good G A β' T' c' := by
  obtain ⟨hT, hinj, hrange, hconn⟩ := h
  have hfin : Finite β := Finite.of_injective c hinj
  have hvc : ∀ b, v ∉ c b := fun b hb => by
    simpa using ((hrange _).1 ⟨b, rfl⟩).1.1 hb
  by_cases hNmax : Maximal (Cl G (A.erase v)) (Nb G A v)
  · obtain ⟨K0, hK0⟩ := (hrange _).2 hNmax
    refine ⟨β, T, Function.update c K0 (insert v (Nb G A v)), hT, ?_, ?_, ?_⟩
    · intro b1 b2 h12
      by_cases h1 : b1 = K0
      · by_cases h2 : b2 = K0
        · rw [h1, h2]
        · exfalso
          rw [h1, Function.update_self, Function.update_of_ne h2] at h12
          exact hvc b2 (h12 ▸ Set.mem_insert _ _)
      · by_cases h2 : b2 = K0
        · exfalso
          rw [h2, Function.update_self, Function.update_of_ne h1] at h12
          exact hvc b1 (h12 ▸ Set.mem_insert _ _)
        · rw [Function.update_of_ne h1, Function.update_of_ne h2] at h12
          exact hinj h12
    · intro s
      rw [max_iff hv hs]
      constructor
      · rintro ⟨b, rfl⟩
        by_cases hb : b = K0
        · right; rw [hb, Function.update_self]
        · left
          rw [Function.update_of_ne hb]
          refine ⟨(hrange _).1 ⟨b, rfl⟩, fun hbN => hb (hinj ?_)⟩
          rw [hbN, hK0]
      · rintro (⟨hm, hne⟩ | rfl)
        · obtain ⟨b, rfl⟩ := (hrange _).2 hm
          have hb : b ≠ K0 := fun hb => hne (hb ▸ hK0)
          exact ⟨b, Function.update_of_ne hb _ _⟩
        · exact ⟨K0, Function.update_self _ _ _⟩
    · intro w hw
      by_cases hwv : w = v
      · subst hwv
        refine conn_singleton T _ K0 (Set.ext fun b => ?_)
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · intro hb
          by_contra hne
          rw [Function.update_of_ne hne] at hb
          exact hvc b hb
        · rintro rfl
          simp
      · have heq : {b | w ∈ Function.update c K0 (insert v (Nb G A v)) b} = {b | w ∈ c b} := by
          ext b
          by_cases hb : b = K0
          · subst hb
            simp only [Set.mem_setOf_eq, Function.update_self, hK0, Set.mem_insert_iff, hwv,
              false_or]
          · simp [Function.update_of_ne hb]
        rw [heq]
        exact hconn w (Finset.mem_erase.2 ⟨hwv, hw⟩)
  · obtain ⟨K, hNK, hKmax⟩ := exists_max_above (cl_Nb hs)
    obtain ⟨K1, hK1⟩ := (hrange K).2 hKmax
    refine ⟨Option β, leaf T K1, fun o => Option.elim o (insert v (Nb G A v)) c,
      leaf_isTree hT K1, ?_, ?_, ?_⟩
    · rintro (_ | a) (_ | b) h12
      · rfl
      · exfalso
        have h12' : insert v (Nb G A v) = c b := h12
        exact hvc b (h12' ▸ Set.mem_insert _ _)
      · exfalso
        have h12' : c a = insert v (Nb G A v) := h12
        exact hvc a (h12' ▸ Set.mem_insert _ _)
      · exact congrArg some (hinj h12)
    · intro s
      rw [max_iff hv hs]
      constructor
      · rintro ⟨o, rfl⟩
        cases o with
        | none => exact Or.inr rfl
        | some b =>
          refine Or.inl ⟨(hrange _).1 ⟨b, rfl⟩, fun hbN => hNmax ?_⟩
          have : c b = Nb G A v := hbN
          exact this ▸ (hrange _).1 ⟨b, rfl⟩
      · rintro (⟨hm, hne⟩ | rfl)
        · obtain ⟨b, rfl⟩ := (hrange _).2 hm
          exact ⟨some b, rfl⟩
        · exact ⟨none, rfl⟩
    · intro w hw
      by_cases hwv : w = v
      · subst hwv
        refine conn_singleton _ _ none (Set.ext fun o => ?_)
        cases o <;> simp [hvc]
      · have hX := hconn w (Finset.mem_erase.2 ⟨hwv, hw⟩)
        by_cases hwN : w ∈ Nb G A v
        · have hwK : K1 ∈ {b | w ∈ c b} := by
            show w ∈ c K1
            rw [hK1]
            exact hNK hwN
          have heq : {o : Option β | w ∈ Option.elim o (insert v (Nb G A v)) c} =
              insert none (Option.some '' {b | w ∈ c b}) := by
            ext o
            cases o <;> simp [hwN, hwv]
          rw [heq]
          exact leaf_conn_insert hX hwK
        · have heq : {o : Option β | w ∈ Option.elim o (insert v (Nb G A v)) c} =
              Option.some '' {b | w ∈ c b} := by
            ext o
            cases o <;> simp [hwN, hwv]
          rw [heq]
          exact leaf_conn_image hX

lemma good_all (hG : GavrilSubtree.Chordal.IsChordal G) :
    ∀ (n : ℕ) (A : Finset V), A.card = n → ∃ (β : Type u) (T : SimpleGraph β) (c : β → Set V),
      Good G A β T c := by
  intro n
  induction n with
  | zero =>
    intro A hA
    rw [Finset.card_eq_zero] at hA
    subst hA
    refine ⟨PUnit.{u + 1}, ⊥, fun _ => ∅, IsTree.of_subsingleton, fun a b _ => Subsingleton.elim a b,
      ?_, fun w hw => absurd hw (Finset.notMem_empty w)⟩
    intro s
    constructor
    · rintro ⟨_, rfl⟩
      refine ⟨⟨by simp, G.isClique_empty⟩, fun t ht _ => ?_⟩
      simpa using ht.1
    · intro hm
      have : s = ∅ := by simpa using hm.1.1
      exact ⟨PUnit.unit, this.symm⟩
  | succ n ih =>
    intro A hA
    have hne : A.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨v, hv, hs⟩ := exists_simp hG A hne
    obtain ⟨β, T, c, h⟩ := ih (A.erase v) (by rw [Finset.card_erase_of_mem hv]; omega)
    exact step hv hs h

end Main

end CliqueTreeAux

theorem solution {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hG : GavrilSubtree.Chordal.IsChordal G) : GavrilSubtree.Chordal.HasCliqueTree G := by
  classical
  obtain ⟨β, T, c, hT, hinj, hrange, hconn⟩ :=
    CliqueTreeAux.good_all hG _ (Finset.univ : Finset V) rfl
  have hCl : CliqueTreeAux.Cl G Finset.univ = G.IsClique :=
    funext fun s => propext ⟨fun h => h.2, fun h => ⟨by simp, h⟩⟩
  simp only [hCl] at hrange
  let e0 : β → GavrilSubtree.Chordal.Cliques G := fun b => ⟨c b, (hrange _).1 ⟨b, rfl⟩⟩
  have he : Function.Bijective e0 := by
    refine ⟨fun a b h => hinj (congrArg Subtype.val h), ?_⟩
    rintro ⟨s, hs⟩
    obtain ⟨b, hb⟩ := (hrange s).2 hs
    exact ⟨b, Subtype.ext hb⟩
  let e : β ≃ GavrilSubtree.Chordal.Cliques G := Equiv.ofBijective e0 he
  refine ⟨T.comap e.symm, ?_, ?_⟩
  · exact (SimpleGraph.Iso.isTree_iff (SimpleGraph.Iso.comap e.symm T).symm).1 hT
  · intro w
    have hw := hconn w (Finset.mem_univ w)
    refine hw.map ⟨fun x => ⟨e x.1, show w ∈ c x.1 from x.2⟩, fun {x y} hxy => ?_⟩ ?_
    · show T.Adj (e.symm (e x.1)) (e.symm (e y.1))
      simpa using hxy
    · rintro ⟨s, hs⟩
      have h2 : c (e.symm s) = s.1 := congrArg Subtype.val (e.apply_symm_apply s)
      exact ⟨⟨e.symm s, show w ∈ c (e.symm s) from h2 ▸ hs⟩, Subtype.ext (e.apply_symm_apply s)⟩
