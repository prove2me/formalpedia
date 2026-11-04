-- Prove2me | solution 1 for GavrilSubtree.Chordal.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-03T23:03:21.129115+00:00
-- url     : https://prove2.me/submissions/aeed5c8d-adea-4399-a947-f3ade0b6469e

import Mathlib
import Definitions.Def_GavrilSubtree_Chordal_Setting

universe u

namespace HellyAux

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

end HellyAux

namespace HellyAux

theorem three_point {β : Type u} (T : SimpleGraph β) (hT : T.IsTree)
    {ι : Type*} (t : ι → Set β) (ht : ∀ i, (T.induce (t i)).Connected) (a₁ a₂ a₃ : β)
    (h : ∀ i, (a₁ ∈ t i ∧ a₂ ∈ t i) ∨ (a₁ ∈ t i ∧ a₃ ∈ t i) ∨ (a₂ ∈ t i ∧ a₃ ∈ t i)) :
    (⋂ i, t i).Nonempty := by
  obtain ⟨m, h12, h13, h23⟩ := HellyAux.median hT a₁ a₂ a₃
  obtain ⟨p12, hp12⟩ := hT.connected.preconnected a₁ a₂ |>.exists_isPath
  obtain ⟨p13, hp13⟩ := hT.connected.preconnected a₁ a₃ |>.exists_isPath
  obtain ⟨p23, hp23⟩ := hT.connected.preconnected a₂ a₃ |>.exists_isPath
  refine ⟨m, Set.mem_iInter.2 fun i => ?_⟩
  rcases h i with ⟨x, y⟩ | ⟨x, y⟩ | ⟨x, y⟩
  · exact HellyAux.path_support_subset hT (ht i) x y p12 hp12 m (h12 p12 hp12)
  · exact HellyAux.path_support_subset hT (ht i) x y p13 hp13 m (h13 p13 hp13)
  · exact HellyAux.path_support_subset hT (ht i) x y p23 hp23 m (h23 p23 hp23)

end HellyAux

namespace HellyAux

theorem helly_finset {V : Type u} {β : Type u} {T : SimpleGraph β} {F : V → Set β}
    (hT : T.IsTree) (hc : ∀ v, (T.induce (F v)).Connected)
    (S : Set V) (hp : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → (F u ∩ F v).Nonempty) :
    ∀ n : ℕ, ∀ A : Finset V, (A : Set V) ⊆ S → A.card = n → (⋂ v ∈ A, F v).Nonempty := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hAS hA
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · obtain rfl | rfl | rfl : n = 0 ∨ n = 1 ∨ n = 2 := by omega
      · obtain rfl := Finset.card_eq_zero.1 hA
        obtain ⟨b⟩ := hT.connected.nonempty
        exact ⟨b, by simp⟩
      · obtain ⟨v, rfl⟩ := Finset.card_eq_one.1 hA
        obtain ⟨⟨b, hb⟩⟩ := (hc v).nonempty
        exact ⟨b, by simpa using hb⟩
      · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hA
        obtain ⟨b, hbx, hby⟩ := hp x (hAS (by simp)) y (hAS (by simp)) hxy
        refine ⟨b, Set.mem_iInter₂.2 fun v hv => ?_⟩
        rcases Finset.mem_insert.1 hv with rfl | hv
        · exact hbx
        · rw [Finset.mem_singleton.1 hv]; exact hby
    · obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card.1 (by omega : 2 < A.card)
      have key : ∀ w ∈ A, ∃ a, a ∈ ⋂ v ∈ A.erase w, F v := by
        intro w hw
        exact ih (A.erase w).card (by rw [Finset.card_erase_of_mem hw]; omega) _
          ((Finset.coe_subset.2 (Finset.erase_subset _ _)).trans hAS) rfl
      obtain ⟨a₁, h₁⟩ := key x hx
      obtain ⟨a₂, h₂⟩ := key y hy
      obtain ⟨a₃, h₃⟩ := key z hz
      rw [Set.mem_iInter₂] at h₁ h₂ h₃
      obtain ⟨m, hm⟩ := three_point T hT
        (ι := A) (fun i => F i) (fun i => hc i) a₁ a₂ a₃ (by
          rintro ⟨v, hv⟩
          by_cases hvx : v = x
          · subst hvx
            exact Or.inr (Or.inr ⟨h₂ v (Finset.mem_erase.2 ⟨hxy, hv⟩),
              h₃ v (Finset.mem_erase.2 ⟨hxz, hv⟩)⟩)
          by_cases hvy : v = y
          · subst hvy
            exact Or.inr (Or.inl ⟨h₁ v (Finset.mem_erase.2 ⟨hxy.symm, hv⟩),
              h₃ v (Finset.mem_erase.2 ⟨hyz, hv⟩)⟩)
          by_cases hvz : v = z
          · subst hvz
            exact Or.inl ⟨h₁ v (Finset.mem_erase.2 ⟨hxz.symm, hv⟩),
              h₂ v (Finset.mem_erase.2 ⟨hyz.symm, hv⟩)⟩
          exact Or.inl ⟨h₁ v (Finset.mem_erase.2 ⟨hvx, hv⟩), h₂ v (Finset.mem_erase.2 ⟨hvy, hv⟩)⟩)
      exact ⟨m, Set.mem_iInter₂.2 fun v hv => Set.mem_iInter.1 hm ⟨v, hv⟩⟩

end HellyAux

theorem solution {V : Type u} {G : SimpleGraph V} {β : Type u} {T : SimpleGraph β}
    {F : V → Set β} (hF : GavrilSubtree.Chordal.IsSubtreeRep G T F) (A : Finset V)
    (hA : G.IsClique (A : Set V)) :
    (⋂ v ∈ A, F v).Nonempty :=
  HellyAux.helly_finset hF.1 hF.2.1 (A : Set V)
    (fun u hu v hv huv => (hF.2.2 u v huv).1 (hA hu hv huv)) A.card A subset_rfl rfl
