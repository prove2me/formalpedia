-- Prove2me | solution 1 for GavrilSubtree.Chordal.isChordal_of_isSubtreeGraph
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-03T23:22:44.032104+00:00
-- url     : https://prove2.me/submissions/102a5b05-de97-4372-a548-d3e21ce6b8a6

import Mathlib
import Definitions.Def_GavrilSubtree_Chordal_Setting

universe u

namespace ChordAux

open SimpleGraph

/-- first hit of a set along a walk -/
theorem first_hit {β : Type*} {T : SimpleGraph β} (S : Set β) :
    ∀ {x y : β} (q : T.Walk x y), y ∈ S →
      ∃ m ∈ S, ∃ (q' : T.Walk x m) (q'' : T.Walk m y), q = q'.append q'' ∧
        ∀ z ∈ q'.support, z ∈ S → z = m := by
  intro x y q
  induction q with
  | nil =>
    intro hy
    exact ⟨_, hy, Walk.nil, Walk.nil, rfl, by simp⟩
  | @cons a b c h q ih =>
    intro hy
    by_cases ha : a ∈ S
    · exact ⟨a, ha, Walk.nil, Walk.cons h q, rfl, by simp⟩
    · obtain ⟨m, hm, q', q'', hq, hz⟩ := ih hy
      refine ⟨m, hm, Walk.cons h q', q'', by simp [hq], ?_⟩
      intro z hz1 hz2
      rw [Walk.support_cons, List.mem_cons] at hz1
      rcases hz1 with rfl | hz1
      · exact absurd hz2 ha
      · exact hz z hz1 hz2

theorem path_eq {β : Type*} {T : SimpleGraph β} (hT : T.IsTree) {u v : β} {p p' : T.Walk u v}
    (hp : p.IsPath) (hp' : p'.IsPath) : p = p' := by
  have := hT.isAcyclic.subsingleton_path u v
  have h1 : (⟨p, hp⟩ : T.Path u v) = ⟨p', hp'⟩ := Subsingleton.elim _ _
  exact congrArg Subtype.val h1

/-- a subtree containing two vertices contains the path between them -/
theorem path_support_subset {β : Type*} {T : SimpleGraph β} (hT : T.IsTree) {t : Set β}
    (ht : (T.induce t).Connected) {a b : β} (ha : a ∈ t) (hb : b ∈ t) (p : T.Walk a b)
    (hp : p.IsPath) : ∀ z ∈ p.support, z ∈ t := by
  classical
  obtain ⟨w⟩ := ht.preconnected ⟨a, ha⟩ ⟨b, hb⟩
  let w' : T.Walk a b := w.map (SimpleGraph.Embedding.induce t).toHom
  have hw' : ∀ z ∈ w'.support, z ∈ t := by
    intro z hz
    have hz' : z ∈ (w.map (SimpleGraph.Embedding.induce t).toHom).support := hz
    rw [Walk.support_map, List.mem_map] at hz'
    obtain ⟨y, _, rfl⟩ := hz'
    exact y.2
  have h2 : w'.bypass = p := path_eq hT w'.bypass_isPath hp
  intro z hz
  rw [← h2] at hz
  exact hw' z (w'.support_bypass_subset_support hz)

theorem median {β : Type*} {T : SimpleGraph β} (hT : T.IsTree) (a₁ a₂ a₃ : β) :
    ∃ m : β, (∀ p : T.Walk a₁ a₂, p.IsPath → m ∈ p.support) ∧
      (∀ p : T.Walk a₁ a₃, p.IsPath → m ∈ p.support) ∧
      (∀ p : T.Walk a₂ a₃, p.IsPath → m ∈ p.support) := by
  classical
  obtain ⟨p, hp⟩ := hT.connected.preconnected a₁ a₂ |>.exists_isPath
  obtain ⟨q, hq⟩ := hT.connected.preconnected a₃ a₁ |>.exists_isPath
  obtain ⟨m, hmS, q', q'', hqq, hz⟩ := first_hit {z | z ∈ p.support} q (p.start_mem_support)
  have hmp : m ∈ p.support := hmS
  have hq' : q'.IsPath := by
    have : (q'.append q'').IsPath := hqq ▸ hq
    exact this.of_append_left
  have hp2 : (p.dropUntil m hmp).IsPath := hp.dropUntil hmp
  have hr : (q'.append (p.dropUntil m hmp)).IsPath := by
    rw [Walk.isPath_def, Walk.support_append, List.nodup_append]
    have h3 := hp2.support_nodup
    rw [← Walk.cons_tail_support, List.nodup_cons] at h3
    refine ⟨hq'.support_nodup, h3.2, ?_⟩
    intro z hz1 z' hz2 hzz
    subst hzz
    have hz3 : z ∈ p.support :=
      p.support_dropUntil_subset_support hmp (List.mem_of_mem_tail hz2)
    have := hz z hz1 hz3
    rw [this] at hz2
    exact h3.1 hz2
  have hmq' : m ∈ q'.support := q'.end_mem_support
  refine ⟨m, ?_, ?_, ?_⟩
  · intro p' hp'
    rw [← path_eq hT hp hp']
    exact hmp
  · intro p' hp'
    have := path_eq hT hp'.reverse hq
    have h4 : m ∈ q.support := by
      rw [hqq, Walk.support_append]
      exact List.mem_append_left _ hmq'
    have h5 : m ∈ p'.reverse.support := by rw [this]; exact h4
    simpa using h5
  · intro p' hp'
    have := path_eq hT hp'.reverse hr
    have h5 : m ∈ p'.reverse.support := by
      rw [this, Walk.support_append]
      exact List.mem_append_left _ hmq'
    simpa using h5
end ChordAux

namespace ChordAux

theorem three_point {β : Type u} (T : SimpleGraph β) (hT : T.IsTree)
    {ι : Type*} (t : ι → Set β) (ht : ∀ i, (T.induce (t i)).Connected) (a₁ a₂ a₃ : β)
    (h : ∀ i, (a₁ ∈ t i ∧ a₂ ∈ t i) ∨ (a₁ ∈ t i ∧ a₃ ∈ t i) ∨ (a₂ ∈ t i ∧ a₃ ∈ t i)) :
    (⋂ i, t i).Nonempty := by
  obtain ⟨m, h12, h13, h23⟩ := ChordAux.median hT a₁ a₂ a₃
  obtain ⟨p12, hp12⟩ := hT.connected.preconnected a₁ a₂ |>.exists_isPath
  obtain ⟨p13, hp13⟩ := hT.connected.preconnected a₁ a₃ |>.exists_isPath
  obtain ⟨p23, hp23⟩ := hT.connected.preconnected a₂ a₃ |>.exists_isPath
  refine ⟨m, Set.mem_iInter.2 fun i => ?_⟩
  rcases h i with ⟨x, y⟩ | ⟨x, y⟩ | ⟨x, y⟩
  · exact ChordAux.path_support_subset hT (ht i) x y p12 hp12 m (h12 p12 hp12)
  · exact ChordAux.path_support_subset hT (ht i) x y p13 hp13 m (h13 p13 hp13)
  · exact ChordAux.path_support_subset hT (ht i) x y p23 hp23 m (h23 p23 hp23)

end ChordAux

namespace ChordAux

open SimpleGraph

theorem key {V : Type u} {β : Type u} {G : SimpleGraph V} {T : SimpleGraph β} {F : V → Set β}
    (hF : GavrilSubtree.Chordal.IsSubtreeRep G T F) :
    ∀ n : ℕ, ∀ {a b : V} (q : G.Walk a b), q.length = n + 2 → q.IsPath →
    ∀ W : Set β, (T.induce W).Connected → (W ∩ F a).Nonempty → (W ∩ F b).Nonempty →
    (∀ x ∈ q.support, x ≠ a → x ≠ b → W ∩ F x = ∅) →
    (∀ x ∈ q.support, ∀ y ∈ q.support, (F x ∩ F y).Nonempty → x = y ∨ s(x, y) ∈ q.edges) →
    False := by
  intro n
  induction n with
  | zero =>
    intro a b q hlen hq W hW ha hb hint hind
    cases q with
    | nil => simp at hlen
    | @cons _ a' _ h q' =>
      cases q' with
      | nil => simp at hlen
      | @cons _ a'' _ h2 q'' =>
        have hq0 : q''.length = 0 := by simpa using hlen
        have hba : a'' = b := q''.eq_of_length_eq_zero hq0
        subst hba
        cases q'' with
        | cons _ _ => simp at hq0
        | nil =>
          rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff] at hq
          simp at hq
          obtain ⟨hq1, hq2, hq3⟩ := hq
          have haa' : a ≠ a' := h.ne
          have ha'a'' : a' ≠ a'' := h2.ne
          have haa'' : a ≠ a'' := hq3
          have e1 : (F a ∩ F a').Nonempty := (hF.2.2 a a' haa').1 h
          have e2 : (F a' ∩ F a'').Nonempty := (hF.2.2 a' a'' ha'a'').1 h2
          have e3 : F a ∩ F a'' = ∅ := by
            by_contra hne
            obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.2 hne
            rcases hind a (by simp) a'' (by simp) ⟨y, hy⟩ with e | e
            · exact haa'' e
            · simp at e
              grind
          have e4 : W ∩ F a' = ∅ := hint a' (by simp) haa'.symm ha'a''
          obtain ⟨x1, hx1⟩ := e1
          obtain ⟨x2, hx2⟩ := e2
          obtain ⟨x3, hx3⟩ := hb
          have hU : (T.induce (W ∪ F a)).Connected :=
            SimpleGraph.induce_union_connected hW.preconnected (hF.2.1 a).preconnected
              (by obtain ⟨y, hy⟩ := ha; exact ⟨y, hy⟩)
          obtain ⟨m, hm⟩ := three_point T hF.1 (ι := Fin 3)
            ![W ∪ F a, F a', F a''] (by intro i; fin_cases i <;> simp [hU, hF.2.1])
            x1 x2 x3 (by
              intro i
              fin_cases i
              · exact Or.inr (Or.inl ⟨Or.inr hx1.1, Or.inl hx3.1⟩)
              · exact Or.inl ⟨hx1.2, hx2.1⟩
              · exact Or.inr (Or.inr ⟨hx2.2, hx3.2⟩))
          have m0 := Set.mem_iInter.1 hm 0
          have m1 := Set.mem_iInter.1 hm 1
          have m2 := Set.mem_iInter.1 hm 2
          simp at m0 m1 m2
          rcases m0 with m0 | m0
          · have : m ∈ W ∩ F a' := ⟨m0, m1⟩
            rw [e4] at this; exact this
          · have : m ∈ F a ∩ F a'' := ⟨m0, m2⟩
            rw [e3] at this; exact this
  | succ n ih =>
    intro a b q hlen hq W hW ha hb hint hind
    cases q with
    | nil => simp at hlen
    | @cons _ a' _ h q' =>
      have hq' : q'.IsPath := ((Walk.cons_isPath_iff h q').1 hq).1
      have hna : a ∉ q'.support := ((Walk.cons_isPath_iff h q').1 hq).2
      have haa' : a ≠ a' := h.ne
      have hlen' : q'.length = n + 2 := by simp at hlen; omega
      have e1 : (F a ∩ F a').Nonempty := (hF.2.2 a a' haa').1 h
      refine ih q' hlen' hq' (W ∪ F a)
        (SimpleGraph.induce_union_connected hW.preconnected (hF.2.1 a).preconnected
          (by obtain ⟨y, hy⟩ := ha; exact ⟨y, hy⟩)) ?_ ?_ ?_ ?_
      · obtain ⟨y, hy⟩ := e1
        exact ⟨y, Or.inr hy.1, hy.2⟩
      · obtain ⟨y, hy⟩ := hb
        exact ⟨y, Or.inl hy.1, hy.2⟩
      · intro x hx hxa' hxb
        have hxa : x ≠ a := fun e => hna (e ▸ hx)
        have h1 : W ∩ F x = ∅ := hint x (by simp [hx]) hxa hxb
        have h2 : F a ∩ F x = ∅ := by
          by_contra hne
          obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.2 hne
          rcases hind a (by simp) x (by simp [hx]) ⟨y, hy⟩ with e | e
          · exact hxa e.symm
          · rw [Walk.edges_cons, List.mem_cons] at e
            rcases e with e | e
            · rw [Sym2.eq_iff] at e
              grind
            · exact hna (Walk.fst_mem_support_of_mem_edges q' e)
        rw [Set.union_inter_distrib_right, h1, h2]
        simp
      · intro x hx y hy hxy
        rcases hind x (by simp [hx]) y (by simp [hy]) hxy with e | e
        · exact Or.inl e
        · right
          rw [Walk.edges_cons, List.mem_cons] at e
          rcases e with e | e
          · rw [Sym2.eq_iff] at e
            exfalso
            grind
          · exact e

end ChordAux

theorem solution {V : Type u} (G : SimpleGraph V)
    (hG : GavrilSubtree.Chordal.IsSubtreeGraph G) : GavrilSubtree.Chordal.IsChordal G := by
  obtain ⟨β, T, F, hF⟩ := hG
  intro u c hc hlen
  by_contra hno
  push Not at hno
  cases c with
  | nil => simp at hlen
  | @cons _ v _ h p =>
    rw [SimpleGraph.Walk.cons_isCycle_iff] at hc
    cases p with
    | nil => simp at hlen
    | @cons _ w _ h2 p' =>
      have hp := hc.1
      rw [SimpleGraph.Walk.cons_isPath_iff] at hp
      obtain ⟨hp', hv⟩ := hp
      simp only [SimpleGraph.Walk.length_cons] at hlen
      refine ChordAux.key hF (p'.length - 2) p' (by omega) hp' (F v) (hF.2.1 v) ?_ ?_ ?_ ?_
      · exact (hF.2.2 v w h2.ne).1 h2
      · rw [Set.inter_comm]; exact (hF.2.2 u v h.ne).1 h
      · intro x hx hxw hxu
        by_contra hne
        obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.2 hne
        have hxv : v ≠ x := fun e => hv (e ▸ hx)
        have hadj : G.Adj v x := (hF.2.2 v x hxv).2 ⟨y, hy⟩
        have := hno v (by simp) x (by simp [hx]) hadj
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at this
        rcases this with e | e | e
        · rw [Sym2.eq_iff] at e; grind
        · rw [Sym2.eq_iff] at e; grind
        · exact hv (SimpleGraph.Walk.fst_mem_support_of_mem_edges p' e)
      · intro x hx y hy hxy
        by_cases hxy' : x = y
        · exact Or.inl hxy'
        right
        have hadj : G.Adj x y := (hF.2.2 x y hxy').2 hxy
        have := hno x (by simp [hx]) y (by simp [hy]) hadj
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at this
        rcases this with e | e | e
        · rw [Sym2.eq_iff] at e; exfalso; grind
        · rw [Sym2.eq_iff] at e; exfalso; grind
        · exact e
