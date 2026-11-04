-- Prove2me | solution 1 for GavrilSubtree.Chordal.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T00:27:54.021207+00:00
-- url     : https://prove2.me/submissions/9c4bcdf9-9303-4bfc-b670-a04e831c09cc

import Mathlib
import Definitions.Def_GavrilSubtree_Chordal_Setting

universe u

namespace Thm2Aux

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

end Thm2Aux

namespace Thm2Aux

theorem three_point {β : Type u} (T : SimpleGraph β) (hT : T.IsTree)
    {ι : Type*} (t : ι → Set β) (ht : ∀ i, (T.induce (t i)).Connected) (a₁ a₂ a₃ : β)
    (h : ∀ i, (a₁ ∈ t i ∧ a₂ ∈ t i) ∨ (a₁ ∈ t i ∧ a₃ ∈ t i) ∨ (a₂ ∈ t i ∧ a₃ ∈ t i)) :
    (⋂ i, t i).Nonempty := by
  obtain ⟨m, h12, h13, h23⟩ := Thm2Aux.median hT a₁ a₂ a₃
  obtain ⟨p12, hp12⟩ := hT.connected.preconnected a₁ a₂ |>.exists_isPath
  obtain ⟨p13, hp13⟩ := hT.connected.preconnected a₁ a₃ |>.exists_isPath
  obtain ⟨p23, hp23⟩ := hT.connected.preconnected a₂ a₃ |>.exists_isPath
  refine ⟨m, Set.mem_iInter.2 fun i => ?_⟩
  rcases h i with ⟨x, y⟩ | ⟨x, y⟩ | ⟨x, y⟩
  · exact Thm2Aux.path_support_subset hT (ht i) x y p12 hp12 m (h12 p12 hp12)
  · exact Thm2Aux.path_support_subset hT (ht i) x y p13 hp13 m (h13 p13 hp13)
  · exact Thm2Aux.path_support_subset hT (ht i) x y p23 hp23 m (h23 p23 hp23)

end Thm2Aux

namespace Thm2Aux

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

end Thm2Aux


namespace Thm2Aux

open SimpleGraph

def RIP {V : Type u} (Λ : Set (Set V)) (r : Set V → ℕ) : Prop :=
  Set.InjOn r Λ ∧ ∀ s ∈ Λ, (∃ u ∈ Λ, r u < r s) →
    ∃ t ∈ Λ, r t < r s ∧ ∀ v ∈ s, (∃ u ∈ Λ, r u < r s ∧ v ∈ u) → v ∈ t

theorem case1 {V β : Type*} (σ : β → Set V) (ℓ w : β) (hwℓ : w ≠ ℓ) (hC : σ ℓ ⊆ σ w)
    (s : Set V) :
    Maximal (· ∈ Set.range σ) s ↔ Maximal (fun s => ∃ q, q ≠ ℓ ∧ σ q = s) s := by
  constructor
  · rintro ⟨⟨q, rfl⟩, hmax⟩
    by_cases hq : q = ℓ
    · have h1 : σ w ⊆ σ q := hmax ⟨w, rfl⟩ (by rw [hq]; exact hC)
      have h2 : σ q = σ w := Set.Subset.antisymm (by rw [hq]; exact hC) h1
      refine ⟨⟨w, hwℓ, h2.symm⟩, ?_⟩
      rintro t ⟨q', _, rfl⟩ hst
      exact hmax ⟨q', rfl⟩ hst
    · refine ⟨⟨q, hq, rfl⟩, ?_⟩
      rintro t ⟨q', _, rfl⟩ hst
      exact hmax ⟨q', rfl⟩ hst
  · rintro ⟨⟨q, hq, rfl⟩, hmax⟩
    refine ⟨⟨q, rfl⟩, ?_⟩
    rintro t ⟨q', rfl⟩ hst
    by_cases hq' : q' = ℓ
    · have h1 : σ w ⊆ σ q := hmax ⟨w, hwℓ, rfl⟩ (hst.trans (by rw [hq']; exact hC))
      rw [hq']
      exact hC.trans h1
    · exact hmax ⟨q', hq', rfl⟩ hst

theorem case2 {V β : Type*} [Finite β] (σ : β → Set V) (ℓ w : β) (hwℓ : w ≠ ℓ)
    (hmeet : ∀ q, q ≠ ℓ → ∀ v, v ∈ σ ℓ → v ∈ σ q → v ∈ σ w)
    (hv0 : ∃ v0 ∈ σ ℓ, v0 ∉ σ w)
    (Λ Λ' : Set (Set V))
    (hΛ : ∀ s, s ∈ Λ ↔ Maximal (· ∈ Set.range σ) s)
    (hΛ' : ∀ s, s ∈ Λ' ↔ Maximal (fun s => ∃ q, q ≠ ℓ ∧ σ q = s) s)
    (r' : Set V → ℕ) (hr' : RIP Λ' r') : ∃ r, RIP Λ r := by
  classical
  obtain ⟨v0, hv0L, hv0w⟩ := hv0
  have hv0q : ∀ q, v0 ∈ σ q → q = ℓ := fun q hq => by
    by_contra hne; exact hv0w (hmeet q hne v0 hv0L hq)
  have hLΛ : σ ℓ ∈ Λ := by
    refine (hΛ _).2 ⟨⟨ℓ, rfl⟩, ?_⟩
    rintro t ⟨q, hq⟩ hLt
    have e : q = ℓ := hv0q q (hq ▸ hLt hv0L)
    exact (hq.symm.trans (congrArg σ e)).le
  have hLΛ' : σ ℓ ∉ Λ' := by
    intro h
    obtain ⟨q, hq, hq2⟩ := ((hΛ' _).1 h).1
    exact hq (hv0q q (hq2 ▸ hv0L))
  have hQ : ∀ s ∈ Λ', ∃ q, q ≠ ℓ ∧ σ q = s := fun s hs => ((hΛ' s).1 hs).1
  have hmeetS : ∀ s ∈ Λ', ∀ v, v ∈ σ ℓ → v ∈ s → v ∈ σ w := by
    intro s hs v hv1 hv2
    obtain ⟨q, hq, rfl⟩ := hQ s hs
    exact hmeet q hq v hv1 hv2
  have F1 : ∀ s ∈ Λ, s ≠ σ ℓ → s ∈ Λ' := by
    intro s hs hne
    obtain ⟨⟨q, rfl⟩, hmax⟩ := (hΛ s).1 hs
    refine (hΛ' _).2 ⟨⟨q, fun h => hne (by rw [h]), rfl⟩, ?_⟩
    rintro t ⟨q', _, rfl⟩ hst
    exact hmax ⟨q', rfl⟩ hst
  have F2b : ∀ s ∈ Λ', s ∉ Λ → s ≤ σ ℓ := by
    intro s hs hsΛ
    by_contra hle
    apply hsΛ
    refine (hΛ s).2 ⟨?_, ?_⟩
    · obtain ⟨q, _, rfl⟩ := hQ s hs
      exact ⟨q, rfl⟩
    · rintro t ⟨q', rfl⟩ hst
      by_cases hq' : q' = ℓ
      · exact absurd (by rw [← hq']; exact hst) hle
      · exact ((hΛ' s).1 hs).2 ⟨q', hq', rfl⟩ hst
  have F2a : ∀ s ∈ Λ', s ≤ σ ℓ → s = σ w := by
    intro s hs hsL
    have h1 : s ≤ σ w := fun v hv => hmeetS s hs v (hsL hv) hv
    exact Set.Subset.antisymm h1 (((hΛ' s).1 hs).2 ⟨w, hwℓ, rfl⟩ h1)
  have hfin : (Set.range σ).Finite := Set.finite_range σ
  have hfinΛ' : Λ'.Finite := hfin.subset (fun s hs => by
    obtain ⟨q, _, rfl⟩ := hQ s hs
    exact ⟨q, rfl⟩)
  by_cases hY : σ w ∈ Λ' ∧ σ w ≤ σ ℓ
  · -- case Y : replace σ w by σ ℓ
    obtain ⟨hW, hWL⟩ := hY
    have hWΛ : σ w ∉ Λ := by
      intro h
      have := ((hΛ _).1 h).2 ⟨ℓ, rfl⟩ hWL
      exact hv0w (this hv0L)
    obtain ⟨r, rL, rO⟩ : ∃ r : Set V → ℕ, r (σ ℓ) = r' (σ w) ∧ ∀ s, s ≠ σ ℓ → r s = r' s :=
      ⟨fun s => if s = σ ℓ then r' (σ w) else r' s, if_pos rfl, fun s hs => if_neg hs⟩
    have hsub : ∀ s ∈ Λ, s ≠ σ ℓ → s ∈ Λ' ∧ s ≠ σ w := fun s hs hne =>
      ⟨F1 s hs hne, fun h => hWΛ (h ▸ hs)⟩
    have hsup : ∀ s ∈ Λ', s ≠ σ w → s ∈ Λ := by
      intro s hs hne
      by_contra hsΛ
      exact hne (F2a s hs (F2b s hs hsΛ))
    have hT : ∀ s ∈ Λ, s ≠ σ ℓ → ∀ v ∈ s, (∃ u ∈ Λ, r u < r s ∧ v ∈ u) →
        ∃ u ∈ Λ', r' u < r' s ∧ v ∈ u := by
      intro s hs hsL v hv ⟨u, hu, hlt, hvu⟩
      have hs' := (hsub s hs hsL).1
      by_cases huL : u = σ ℓ
      · subst huL
        rw [rL, rO s hsL] at hlt
        exact ⟨σ w, hW, hlt, hmeetS s hs' v hvu hv⟩
      · rw [rO u huL, rO s hsL] at hlt
        exact ⟨u, F1 u hu huL, hlt, hvu⟩
    refine ⟨r, ?_, ?_⟩
    · intro s hs t ht hst
      by_cases hsL : s = σ ℓ <;> by_cases htL : t = σ ℓ
      · rw [hsL, htL]
      · exfalso
        rw [hsL, rL, rO t htL] at hst
        exact (hsub t ht htL).2 (hr'.1 hW (hsub t ht htL).1 hst).symm
      · exfalso
        rw [htL, rL, rO s hsL] at hst
        exact (hsub s hs hsL).2 (hr'.1 hW (hsub s hs hsL).1 hst.symm).symm
      · rw [rO s hsL, rO t htL] at hst
        exact hr'.1 (hsub s hs hsL).1 (hsub t ht htL).1 hst
    · intro s hs ⟨u, hu, hlt⟩
      by_cases hsL : s = σ ℓ
      · subst hsL
        rw [rL] at hlt
        have huL : u ≠ σ ℓ := fun h => by rw [h, rL] at hlt; exact lt_irrefl _ hlt
        rw [rO u huL] at hlt
        obtain ⟨t, ht, hlt', hall⟩ := hr'.2 (σ w) hW ⟨u, (hsub u hu huL).1, hlt⟩
        have htW : t ≠ σ w := fun h => by rw [h] at hlt'; exact lt_irrefl _ hlt'
        have htL : t ≠ σ ℓ := fun h => hLΛ' (h ▸ ht)
        refine ⟨t, hsup t ht htW, ?_, ?_⟩
        · rw [rL, rO t htL]; exact hlt'
        · rintro v hv ⟨u', hu', hlt2, hvu'⟩
          rw [rL] at hlt2
          have hu'L : u' ≠ σ ℓ := fun h => by rw [h, rL] at hlt2; exact lt_irrefl _ hlt2
          rw [rO u' hu'L] at hlt2
          exact hall v (hmeetS u' (hsub u' hu' hu'L).1 v hv hvu') ⟨u', (hsub u' hu' hu'L).1, hlt2, hvu'⟩
      · have hs' := hsub s hs hsL
        have hex : ∃ u ∈ Λ', r' u < r' s := by
          by_cases huL : u = σ ℓ
          · subst huL
            rw [rL, rO s hsL] at hlt
            exact ⟨σ w, hW, hlt⟩
          · rw [rO u huL, rO s hsL] at hlt
            exact ⟨u, F1 u hu huL, hlt⟩
        obtain ⟨t, ht, hlt', hall⟩ := hr'.2 s hs'.1 hex
        by_cases htW : t = σ w
        · refine ⟨σ ℓ, hLΛ, ?_, ?_⟩
          · rw [rL, rO s hsL, ← htW]; exact hlt'
          · intro v hv hex2
            have := hall v hv (hT s hs hsL v hv hex2)
            rw [htW] at this
            exact hWL this
        · have htL : t ≠ σ ℓ := fun h => hLΛ' (h ▸ ht)
          refine ⟨t, hsup t ht htW, ?_, ?_⟩
          · rw [rO s hsL, rO t htL]; exact hlt'
          · intro v hv hex2
            exact hall v hv (hT s hs hsL v hv hex2)
  · -- case X : add σ ℓ as a new last element
    have hΛ'Λ : ∀ s ∈ Λ', s ∈ Λ := by
      intro s hs
      by_contra hsΛ
      exact hY ⟨F2a s hs (F2b s hs hsΛ) ▸ hs, F2a s hs (F2b s hs hsΛ) ▸ F2b s hs hsΛ⟩
    obtain ⟨B, hB⟩ := (hfinΛ'.image r').bddAbove
    have hN : ∀ s ∈ Λ', r' s < B + 1 := fun s hs => Nat.lt_succ_of_le (hB ⟨s, hs, rfl⟩)
    obtain ⟨M, hwM, hM⟩ := Set.Finite.exists_le_maximal
      (hfin.subset (fun s ⟨q, _, h⟩ => ⟨q, h⟩) : {s : Set V | ∃ q, q ≠ ℓ ∧ σ q = s}.Finite)
      (show σ w ∈ {s : Set V | ∃ q, q ≠ ℓ ∧ σ q = s} from ⟨w, hwℓ, rfl⟩)
    have hMΛ' : M ∈ Λ' := (hΛ' M).2 hM
    obtain ⟨r, rL, rO⟩ : ∃ r : Set V → ℕ, r (σ ℓ) = B + 1 ∧ ∀ s, s ≠ σ ℓ → r s = r' s :=
      ⟨fun s => if s = σ ℓ then B + 1 else r' s, if_pos rfl, fun s hs => if_neg hs⟩
    have hne : ∀ s ∈ Λ', s ≠ σ ℓ := fun s hs h => hLΛ' (h ▸ hs)
    refine ⟨r, ?_, ?_⟩
    · intro s hs t ht hst
      by_cases hsL : s = σ ℓ <;> by_cases htL : t = σ ℓ
      · rw [hsL, htL]
      · exfalso
        rw [hsL, rL, rO t htL] at hst
        have := hN t (F1 t ht htL)
        omega
      · exfalso
        rw [htL, rL, rO s hsL] at hst
        have := hN s (F1 s hs hsL)
        omega
      · rw [rO s hsL, rO t htL] at hst
        exact hr'.1 (F1 s hs hsL) (F1 t ht htL) hst
    · intro s hs ⟨u, hu, hlt⟩
      by_cases hsL : s = σ ℓ
      · subst hsL
        refine ⟨M, hΛ'Λ M hMΛ', ?_, ?_⟩
        · rw [rL, rO M (hne M hMΛ')]; exact hN M hMΛ'
        · rintro v hv ⟨u', hu', hlt2, hvu'⟩
          have hu'L : u' ≠ σ ℓ := fun h => by rw [h, rL] at hlt2; exact lt_irrefl _ hlt2
          exact hwM (hmeetS u' (F1 u' hu' hu'L) v hv hvu')
      · have hs' := F1 s hs hsL
        have huL : u ≠ σ ℓ := fun h => by
          rw [h, rL, rO s hsL] at hlt
          have := hN s hs'
          omega
        rw [rO u huL, rO s hsL] at hlt
        obtain ⟨t, ht, hlt', hall⟩ := hr'.2 s hs' ⟨u, F1 u hu huL, hlt⟩
        refine ⟨t, hΛ'Λ t ht, ?_, ?_⟩
        · rw [rO s hsL, rO t (hne t ht)]; exact hlt'
        · rintro v hv ⟨u', hu', hlt2, hvu'⟩
          have hu'L : u' ≠ σ ℓ := fun h => by
            rw [h, rL, rO s hsL] at hlt2
            have := hN s hs'
            omega
          rw [rO u' hu'L, rO s hsL] at hlt2
          exact hall v hv ⟨u', F1 u' hu' hu'L, hlt2, hvu'⟩

theorem rip_tree {V : Type u} (Λ : Set (Set V)) [Finite Λ] (hΛ : Λ.Nonempty)
    (r : Set V → ℕ) (hrip : RIP Λ r) :
    ∃ T : SimpleGraph Λ, T.IsTree ∧
      ∀ v, (∃ s ∈ Λ, v ∈ s) → (T.induce {s : Λ | v ∈ s.1}).Connected := by
  classical
  obtain ⟨hinj, hr⟩ := hrip
  have : Nonempty Λ := hΛ.to_subtype
  have hpar : ∀ x : Λ, ∃ y : Λ, ((∃ u ∈ Λ, r u < r x.1) →
      r y.1 < r x.1 ∧ ∀ v ∈ x.1, (∃ u ∈ Λ, r u < r x.1 ∧ v ∈ u) → v ∈ y.1) ∧
      (¬ (∃ u ∈ Λ, r u < r x.1) → y = x) := by
    intro x
    by_cases h : ∃ u ∈ Λ, r u < r x.1
    · obtain ⟨t, ht, h1, h2⟩ := hr x.1 x.2 h
      exact ⟨⟨t, ht⟩, fun _ => ⟨h1, h2⟩, fun h' => absurd h h'⟩
    · exact ⟨x, fun h' => absurd h' h, fun _ => rfl⟩
  choose par hpar using hpar
  let T : SimpleGraph Λ := SimpleGraph.fromRel (fun x y => par x = y)
  have hTadj : ∀ x y, T.Adj x y ↔ x ≠ y ∧ (par x = y ∨ par y = x) := fun x y => by
    simp [T, SimpleGraph.fromRel_adj]
  obtain ⟨x0, hx0⟩ := Finite.exists_min (fun x : Λ => r x.1)
  have hx0' : ∀ x : Λ, x ≠ x0 → r x0.1 < r x.1 := by
    intro x hx
    refine lt_of_le_of_ne (hx0 x) fun h => hx ?_
    exact Subtype.ext (hinj x0.2 x.2 h).symm
  have hnon : ∀ x : Λ, x ≠ x0 → par x ≠ x := by
    intro x hx h
    have h1 : ∃ u ∈ Λ, r u < r x.1 := ⟨x0.1, x0.2, hx0' x hx⟩
    obtain ⟨h2, -⟩ := (hpar x).1 h1
    rw [h] at h2; exact lt_irrefl _ h2
  have hconn : T.Connected := by
    rw [connected_iff_exists_forall_reachable]
    refine ⟨x0, fun x => ?_⟩
    suffices H : ∀ n, ∀ x : Λ, r x.1 = n → T.Reachable x x0 from (H _ x rfl).symm
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro x hn
    by_cases hx : x = x0
    · subst hx; exact Reachable.refl _
    · have h1 : ∃ u ∈ Λ, r u < r x.1 := ⟨x0.1, x0.2, hx0' x hx⟩
      obtain ⟨h2, -⟩ := (hpar x).1 h1
      have hadj : T.Adj x (par x) := (hTadj _ _).2 ⟨(hnon x hx).symm, Or.inl rfl⟩
      exact hadj.reachable.trans (ih _ (hn ▸ h2) (par x) rfl)
  have hcard : Nat.card T.edgeSet + 1 = Nat.card Λ := by
    have h1 := hconn.card_vert_le_card_edgeSet_add_one
    let f : {x : Λ // x ≠ x0} → T.edgeSet := fun x =>
      ⟨s(x.1, par x.1), (hTadj _ _).2 ⟨(hnon x.1 x.2).symm, Or.inl rfl⟩⟩
    have hf : Function.Surjective f := by
      rintro ⟨e, he⟩
      induction e using Sym2.ind with
      | _ a b =>
      have hadj : T.Adj a b := he
      obtain ⟨hab, h | h⟩ := (hTadj _ _).1 hadj
      · have hax : a ≠ x0 := by
          rintro rfl
          have := (hpar a).2 (fun ⟨u, hu, hlt⟩ => absurd (hx0 ⟨u, hu⟩) (not_le.2 hlt))
          exact hab (by rw [← h, this])
        exact ⟨⟨a, hax⟩, Subtype.ext (by simp [f, h])⟩
      · have hbx : b ≠ x0 := by
          rintro rfl
          have := (hpar b).2 (fun ⟨u, hu, hlt⟩ => absurd (hx0 ⟨u, hu⟩) (not_le.2 hlt))
          exact hab (by rw [← h, this])
        exact ⟨⟨b, hbx⟩, Subtype.ext (by simp [f, h, Sym2.eq_swap])⟩
    have h2 := Nat.card_le_card_of_surjective f hf
    have h3 : Nat.card {x : Λ // x ≠ x0} + 1 = Nat.card Λ := by
      have := Fintype.ofFinite Λ
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_add_one (Finset.mem_univ _), Finset.card_univ]
    omega
  have htree : T.IsTree := isTree_iff_connected_and_card.2 ⟨hconn, hcard⟩
  refine ⟨T, htree, ?_⟩
  rintro v ⟨s, hs, hv⟩
  have hne : ({s : Λ | v ∈ s.1}).Nonempty := ⟨⟨s, hs⟩, hv⟩
  obtain ⟨z0, hz0, hz0min⟩ : ∃ z0 ∈ {s : Λ | v ∈ s.1}, ∀ z ∈ {s : Λ | v ∈ s.1}, r z0.1 ≤ r z.1 := by
    have : Nonempty {s : Λ | v ∈ s.1} := hne.to_subtype
    obtain ⟨z, hz⟩ := Finite.exists_min (fun z : {s : Λ | v ∈ s.1} => r z.1.1)
    exact ⟨z.1, z.2, fun y hy => hz ⟨y, hy⟩⟩
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨z0, hz0⟩, fun x => ?_⟩
  obtain ⟨x, hx⟩ := x
  suffices H : ∀ n, ∀ (x : Λ) (hx : x ∈ {s : Λ | v ∈ s.1}), r x.1 = n →
      (T.induce {s : Λ | v ∈ s.1}).Reachable ⟨x, hx⟩ ⟨z0, hz0⟩ from (H _ x hx rfl).symm
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hx hn
  by_cases hxz : x = z0
  · subst hxz; exact Reachable.refl _
  · have hlt : r z0.1 < r x.1 := lt_of_le_of_ne (hz0min x hx) fun h =>
      hxz (Subtype.ext (hinj z0.2 x.2 h).symm)
    have h1 : ∃ u ∈ Λ, r u < r x.1 := ⟨z0.1, z0.2, hlt⟩
    obtain ⟨h2, h3⟩ := (hpar x).1 h1
    have hvp : v ∈ (par x).1 := h3 v hx ⟨z0.1, z0.2, hlt, hz0⟩
    have hpx : par x ≠ x := fun h => by rw [h] at h2; exact lt_irrefl _ h2
    have hadj : (T.induce {s : Λ | v ∈ s.1}).Adj ⟨x, hx⟩ ⟨par x, hvp⟩ :=
      (hTadj _ _).2 ⟨hpx.symm, Or.inl rfl⟩
    exact hadj.reachable.trans (ih _ (hn ▸ h2) (par x) hvp rfl)

theorem helly_clique {V : Type u} {G : SimpleGraph V} {β : Type u} {T : SimpleGraph β}
    {F : V → Set β} (hT : T.IsTree) (hc : ∀ v, (T.induce (F v)).Connected)
    (hadj : ∀ u v, u ≠ v → (G.Adj u v ↔ (F u ∩ F v).Nonempty)) (A : Finset V)
    (hA : G.IsClique (A : Set V)) : (⋂ v ∈ A, F v).Nonempty :=
  helly_finset hT hc (A : Set V) (fun u hu v hv huv => (hadj u v huv).1 (hA hu hv huv))
    A.card A subset_rfl rfl

theorem card_ne_succ {α : Type*} [Finite α] (a : α) :
    Nat.card {x : α // x ≠ a} + 1 = Nat.card α := by
  have := Fintype.ofFinite α
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_add_one (Finset.mem_univ _),
    Finset.card_univ]

noncomputable def inducedIso {β : Type*} (T : SimpleGraph β) (W : Set β) (Z : Set W) :
    (T.induce W).induce Z ≃g T.induce (Subtype.val '' Z) where
  toEquiv := Equiv.Set.image Subtype.val Z Subtype.val_injective
  map_rel_iff' := Iff.rfl

theorem inter_connected {β : Type*} {T : SimpleGraph β} (hT : T.IsTree) {A B : Set β}
    (hA : (T.induce A).Connected) (hB : (T.induce B).Connected) (hne : (A ∩ B).Nonempty) :
    (T.induce (A ∩ B)).Connected := by
  classical
  obtain ⟨a0, ha0⟩ := hne
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨a0, ha0⟩, ?_⟩
  rintro ⟨b, hb⟩
  obtain ⟨p, hp⟩ := (hT.connected.preconnected a0 b).exists_isPath
  have h1 := path_support_subset hT hA ha0.1 hb.1 p hp
  have h2 := path_support_subset hT hB ha0.2 hb.2 p hp
  exact ⟨p.induce (A ∩ B) (fun z hz => ⟨h1 z hz, h2 z hz⟩)⟩

theorem exists_adj_of_preconn {β : Type*} {T : SimpleGraph β} {Z : Set β}
    (h : (T.induce Z).Preconnected) {a b : β} (ha : a ∈ Z) (hb : b ∈ Z) (hab : a ≠ b) :
    ∃ c ∈ Z, T.Adj a c := by
  obtain ⟨p⟩ := h ⟨a, ha⟩ ⟨b, hb⟩
  have hne : (⟨a, ha⟩ : Z) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Subtype.val h)
  have := p.adj_snd (Walk.not_nil_of_ne hne)
  exact ⟨p.snd.1, p.snd.2, this⟩

theorem conn_remove_leaf {β : Type*} {T : SimpleGraph β} {Z : Set β}
    (hZ : (T.induce Z).Connected) {ℓ w : β} (hw : ∀ y, T.Adj ℓ y → y = w)
    (hne : ∃ x ∈ Z, x ≠ ℓ) : (T.induce (Z ∩ {ℓ}ᶜ)).Connected := by
  obtain ⟨x, hxZ, hxℓ⟩ := hne
  have hs : ∀ y : Z, y ∉ {y : Z | y.1 ≠ ℓ} → ((T.induce Z).neighborSet y).Subsingleton := by
    intro y hy a ha b hb
    have hyl : y.1 = ℓ := by simpa using hy
    have ha' : T.Adj ℓ a.1 := by
      have : T.Adj y.1 a.1 := ha
      rwa [hyl] at this
    have hb' : T.Adj ℓ b.1 := by
      have : T.Adj y.1 b.1 := hb
      rwa [hyl] at this
    exact Subtype.ext ((hw _ ha').trans (hw _ hb').symm)
  have hp := hZ.preconnected.induce_of_degree_eq_one hs
  have himg : Subtype.val '' {y : Z | y.1 ≠ ℓ} = Z ∩ {ℓ}ᶜ := by
    ext y; constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y.2, hy⟩
    · rintro ⟨hy, hyℓ⟩; exact ⟨⟨y, hy⟩, hyℓ, rfl⟩
  rw [← himg]
  have hp' := (SimpleGraph.Iso.preconnected_iff (inducedIso T Z {y : Z | y.1 ≠ ℓ})).1 hp
  exact (connected_iff _).2 ⟨hp', ⟨⟨x, ⟨⟨x, hxZ⟩, hxℓ, rfl⟩⟩⟩⟩

theorem core {V : Type u} (n : ℕ) : ∀ (β : Type u) [Finite β] (T : SimpleGraph β),
    Nat.card β = n + 1 → T.IsTree → ∀ σ : β → Set V,
    (∀ v, (∃ x, v ∈ σ x) → (T.induce {x | v ∈ σ x}).Connected) →
    ∀ Λ : Set (Set V), (∀ s, s ∈ Λ ↔ Maximal (· ∈ Set.range σ) s) → ∃ r, RIP Λ r := by
  induction n with
  | zero =>
    intro β _ T hcard hT σ hμ Λ hΛ
    obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.1 hcard
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro s hs t ht _
      obtain ⟨⟨a, rfl⟩, -⟩ := (hΛ s).1 hs
      obtain ⟨⟨b, rfl⟩, -⟩ := (hΛ t).1 ht
      rw [hsub.elim a b]
    · rintro s hs ⟨u, _, h⟩
      exact absurd h (lt_irrefl 0)
  | succ n ih =>
    intro β _ T hcard hT σ hμ Λ hΛ
    have := Fintype.ofFinite β
    classical
    have hnt : Nontrivial β := by
      rw [← Fintype.one_lt_card_iff_nontrivial]
      rw [Nat.card_eq_fintype_card] at hcard
      omega
    obtain ⟨ℓ, hℓ⟩ := hT.exists_vert_degree_one_of_nontrivial
    obtain ⟨w, hw, hwu⟩ := degree_eq_one_iff_existsUnique_adj.mp hℓ
    have hwℓ : w ≠ ℓ := hw.ne.symm
    have hT'c : (T.induce ({ℓ}ᶜ : Set β)).Connected :=
      hT.connected.induce_compl_singleton_of_degree_eq_one hℓ
    have hT' : (T.induce ({ℓ}ᶜ : Set β)).IsTree := ⟨hT'c, hT.isAcyclic.induce _⟩
    have hcard' : Nat.card ({ℓ}ᶜ : Set β) = n + 1 := by
      have h1 := card_ne_succ ℓ
      have h2 : Nat.card ({ℓ}ᶜ : Set β) = Nat.card {x : β // x ≠ ℓ} :=
        Nat.card_congr (Equiv.subtypeEquivRight fun x => Set.mem_compl_singleton_iff)
      omega
    let σ' : ({ℓ}ᶜ : Set β) → Set V := fun x => σ x.1
    have hconnw : ∀ v, v ∈ σ ℓ → (∃ x, x ≠ ℓ ∧ v ∈ σ x) → v ∈ σ w := by
      rintro v hv ⟨x, hxℓ, hx⟩
      have hZ := hμ v ⟨ℓ, hv⟩
      obtain ⟨c, hc, hadj⟩ := exists_adj_of_preconn hZ.preconnected
        (show ℓ ∈ {x | v ∈ σ x} from hv) (show x ∈ {x | v ∈ σ x} from hx) hxℓ.symm
      rw [hwu c hadj] at hc
      exact hc
    have hmeet : ∀ q, q ≠ ℓ → ∀ v, v ∈ σ ℓ → v ∈ σ q → v ∈ σ w :=
      fun q hq v hv1 hv2 => hconnw v hv1 ⟨q, hq, hv2⟩
    have hμ' : ∀ v, (∃ x, v ∈ σ' x) →
        ((T.induce ({ℓ}ᶜ : Set β)).induce {x | v ∈ σ' x}).Connected := by
      rintro v ⟨x, hx⟩
      have hZ := hμ v ⟨x.1, hx⟩
      refine (SimpleGraph.Iso.connected_iff (inducedIso T _ _)).2 ?_
      have himg : Subtype.val '' {x : ({ℓ}ᶜ : Set β) | v ∈ σ' x} = {y | v ∈ σ y} ∩ {ℓ}ᶜ := by
        ext y; constructor
        · rintro ⟨x, hx, rfl⟩; exact ⟨hx, x.2⟩
        · rintro ⟨hy, hyℓ⟩; exact ⟨⟨y, hyℓ⟩, hy, rfl⟩
      rw [himg]
      exact conn_remove_leaf hZ hwu ⟨x.1, hx, x.2⟩
    have hP' : (fun s => s ∈ Set.range σ') = (fun s => ∃ q, q ≠ ℓ ∧ σ q = s) := by
      funext s; apply propext; constructor
      · rintro ⟨x, rfl⟩; exact ⟨x.1, x.2, rfl⟩
      · rintro ⟨q, hq, rfl⟩; exact ⟨⟨q, hq⟩, rfl⟩
    obtain ⟨r', hr'⟩ := ih ({ℓ}ᶜ : Set β) (T.induce {ℓ}ᶜ) hcard' hT' σ' hμ'
      {s | Maximal (fun s => ∃ q, q ≠ ℓ ∧ σ q = s) s} (fun s => by rw [Set.mem_ofPred_eq, hP'])
    by_cases hC1 : σ ℓ ⊆ σ w
    · have hΛeq : Λ = {s | Maximal (fun s => ∃ q, q ≠ ℓ ∧ σ q = s) s} := by
        ext s; rw [hΛ s, Set.mem_ofPred_eq]; exact case1 σ ℓ w hwℓ hC1 s
      rw [hΛeq]
      exact ⟨r', hr'⟩
    · exact case2 σ ℓ w hwℓ hmeet (Set.not_subset.1 hC1) Λ
        {s | Maximal (fun s => ∃ q, q ≠ ℓ ∧ σ q = s) s} hΛ (fun s => Iff.rfl) r' hr'

theorem exists_max_clique {V : Type u} [Finite V] (G : SimpleGraph V) (s : Set V)
    (hs : G.IsClique s) : ∃ K, Maximal G.IsClique K ∧ s ⊆ K := by
  obtain ⟨K, hsK, hK⟩ := Finite.exists_le_maximal (p := G.IsClique) hs
  exact ⟨K, hK, hsK⟩

theorem forward {V : Type u} [Finite V] (G : SimpleGraph V) {β : Type u} (T : SimpleGraph β)
    (F : V → Set β) (hT : T.IsTree) (hc : ∀ v, (T.induce (F v)).Connected)
    (hadj : ∀ u v, u ≠ v → (G.Adj u v ↔ (F u ∩ F v).Nonempty)) :
    ∃ T' : SimpleGraph {s : Set V // Maximal G.IsClique s}, T'.IsTree ∧
      ∀ v, (T'.induce {A | v ∈ A.1}).Connected := by
  classical
  let Λ : Set (Set V) := {s | Maximal G.IsClique s}
  have hp : ∀ K : Λ, ∃ b, ∀ v ∈ K.1, b ∈ F v := by
    intro K
    have hfin := Set.toFinite K.1
    obtain ⟨b, hb⟩ := helly_clique (G := G) hT hc hadj hfin.toFinset
      (by rw [Set.Finite.coe_toFinset]; exact K.2.1)
    exact ⟨b, fun v hv => Set.mem_iInter₂.1 hb v ((Set.Finite.mem_toFinset hfin).2 hv)⟩
  choose p hp using hp
  have := Fintype.ofFinite Λ
  obtain ⟨K0, hK0, -⟩ := exists_max_clique G ∅ (Set.pairwise_empty _)
  have tn : (Finset.univ.image p).Nonempty := ⟨p ⟨K0, hK0⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  obtain ⟨S, htS, hSconn⟩ := SimpleGraph.extend_finset_to_connected hT.connected.preconnected tn
  obtain ⟨SS, hSfin, hpS, hSconn⟩ : ∃ SS : Set β, SS.Finite ∧ (∀ K : Λ, p K ∈ SS) ∧
      (T.induce SS).Connected :=
    ⟨S, S.finite_toSet, fun K => htS (Finset.mem_image_of_mem _ (Finset.mem_univ _)), hSconn⟩
  have hT' : (T.induce SS).IsTree := ⟨hSconn, hT.isAcyclic.induce _⟩
  let σ : ↥SS → Set V := fun x => {v | x.1 ∈ F v}
  have hμ : ∀ v, (∃ x, v ∈ σ x) → ((T.induce SS).induce {x | v ∈ σ x}).Connected := by
    rintro v ⟨x, hx⟩
    refine (SimpleGraph.Iso.connected_iff (inducedIso T _ _)).2 ?_
    have himg : Subtype.val '' {x : ↥SS | v ∈ σ x} = F v ∩ SS := by
      ext y; constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨hx, x.2⟩
      · rintro ⟨hy, hyS⟩; exact ⟨⟨y, hyS⟩, hy, rfl⟩
    rw [himg]
    exact inter_connected hT (hc v) hSconn ⟨x.1, hx, x.2⟩
  have hclique : ∀ x, G.IsClique (σ x) := fun x u hu v hv huv =>
    (hadj u v huv).2 ⟨x.1, hu, hv⟩
  have hKσ : ∀ K : Λ, K.1 = σ ⟨p K, hpS K⟩ := fun K =>
    Set.Subset.antisymm (fun v hv => hp K v hv)
      (K.2.2 (hclique _) (fun v hv => hp K v hv))
  have hmax : ∀ s, s ∈ Λ ↔ Maximal (· ∈ Set.range σ) s := by
    intro s
    constructor
    · intro hs
      refine ⟨⟨_, (hKσ ⟨s, hs⟩).symm⟩, ?_⟩
      rintro t ⟨x, rfl⟩ hst
      exact hs.2 (hclique x) hst
    · rintro ⟨⟨x, rfl⟩, hmx⟩
      obtain ⟨K, hK, hsK⟩ := exists_max_clique G _ (hclique x)
      have e : K = σ ⟨p ⟨K, hK⟩, hpS _⟩ := hKσ ⟨K, hK⟩
      have h1 : K ⊆ σ x :=
        e.le.trans (hmx (⟨_, rfl⟩ : σ ⟨p ⟨K, hK⟩, hpS _⟩ ∈ Set.range σ) (hsK.trans e.le))
      have h2 : σ x = K := Set.Subset.antisymm hsK h1
      rw [h2]; exact hK
  have hnonempty : Nonempty ↥SS := ⟨⟨p ⟨K0, hK0⟩, hpS _⟩⟩
  have hfinS : Finite ↥SS := hSfin.to_subtype
  have hpos : 0 < Nat.card ↥SS := Nat.card_pos
  obtain ⟨n, hn⟩ : ∃ n, Nat.card ↥SS = n + 1 := ⟨Nat.card ↥SS - 1, by omega⟩
  obtain ⟨r, hr⟩ := core n ↥SS (T.induce SS) hn hT' σ hμ Λ hmax
  obtain ⟨T'', hT'', hcon⟩ := rip_tree Λ ⟨K0, hK0⟩ r hr
  refine ⟨T'', hT'', fun v => hcon v ?_⟩
  obtain ⟨K, hK, hsK⟩ := exists_max_clique G {v} (Set.pairwise_singleton _ _)
  exact ⟨K, hK, hsK rfl⟩

theorem backward {V : Type u} [Finite V] (G : SimpleGraph V)
    (T : SimpleGraph (GavrilSubtree.Chordal.Cliques G)) (hT : T.IsTree)
    (hc : ∀ v, (T.induce (GavrilSubtree.Chordal.cliquesAt G v)).Connected) :
    GavrilSubtree.Chordal.IsSubtreeRep G T (GavrilSubtree.Chordal.cliquesAt G) := by
  refine ⟨hT, hc, fun u v huv => ⟨fun h => ?_, fun ⟨K, hu, hv⟩ => K.2.1 hu hv huv⟩⟩
  have hcl : G.IsClique ({u, v} : Set V) := by
    intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact h
    · exact h.symm
    · exact absurd rfl hxy
  obtain ⟨K, hK, hsub⟩ := exists_max_clique G _ hcl
  exact ⟨⟨K, hK⟩, hsub (by simp), hsub (by simp)⟩

end Thm2Aux

theorem solution {V : Type u} [Fintype V] (G : SimpleGraph V) :
    GavrilSubtree.Chordal.IsSubtreeGraph G ↔ GavrilSubtree.Chordal.HasCliqueTree G := by
  have : Finite V := Finite.of_fintype V
  constructor
  · rintro ⟨β, T, F, hT, hc, hadj⟩
    exact Thm2Aux.forward G T F hT hc hadj
  · rintro ⟨T, hT, hc⟩
    exact ⟨_, T, _, Thm2Aux.backward G T hT hc⟩

