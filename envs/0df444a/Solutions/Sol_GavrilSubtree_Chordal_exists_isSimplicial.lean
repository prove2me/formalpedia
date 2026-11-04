-- Prove2me | solution 1 for GavrilSubtree.Chordal.exists_isSimplicial
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-03T23:22:45.068107+00:00
-- url     : https://prove2.me/submissions/8d4f77a7-c4f2-461a-b58c-0630c254ce2d

import Mathlib
import Definitions.Def_GavrilSubtree_Chordal_Setting

universe u

namespace DiracAux

open SimpleGraph

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

end DiracAux

/-- Dirac–Rose: every finite nonempty chordal graph has a simplicial vertex. -/
theorem solution {V : Type u} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (hG : GavrilSubtree.Chordal.IsChordal G) : ∃ v, GavrilSubtree.Chordal.IsSimplicial G v := by
  classical
  rcases DiracAux.dirac_aux hG _ Finset.univ rfl with h | ⟨a, _, b, _, _, _, ha, _⟩
  · obtain ⟨v⟩ := ‹Nonempty V›
    refine ⟨v, ?_⟩
    intro y _ z _ hyz
    exact h y (Finset.mem_univ _) z (Finset.mem_univ _) hyz
  · refine ⟨a, ?_⟩
    intro y hy z hz hyz
    exact ha y (Finset.mem_univ _) z (Finset.mem_univ _) hy hz hyz
