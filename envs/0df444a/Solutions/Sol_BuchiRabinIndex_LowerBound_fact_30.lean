-- Prove2me | solution 1 for BuchiRabinIndex.LowerBound.fact_30
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T16:28:14.251626+00:00
-- url     : https://prove2.me/submissions/bfae182a-8d14-43ec-bcfe-22218802c05e

import Definitions.Def_BuchiRabinIndex_LowerBound_Nodes

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound.Fact30Aux
open BuchiRabinIndex.LowerBound
open scoped Classical

lemma mem_chain_cons (i : ℕ) (v y : Node) :
    y ∈ chain (i :: v) ↔
      y = [] ∨ (∃ j, 1 ≤ j ∧ j ≤ i - 1 ∧ y = [j]) ∨ ∃ y', y' ∈ chain v ∧ y = i :: y' := by
  simp only [chain, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro (h | ⟨j, hj, rfl⟩ | ⟨y', hy', rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨j, hj.1, hj.2, rfl⟩)
    · exact Or.inr (Or.inr ⟨y', hy', rfl⟩)
  · rintro (h | ⟨j, h1, h2, rfl⟩ | ⟨y', hy', rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨j, ⟨h1, h2⟩, rfl⟩)
    · exact Or.inr (Or.inr ⟨y', hy', rfl⟩)

lemma nil_mem (x : Node) : [] ∈ chain x := by
  cases x with
  | nil => simp [chain]
  | cons i v => exact (mem_chain_cons i v []).2 (Or.inl rfl)

lemma self_mem : ∀ x : Node, x ∈ chain x
  | [] => by simp [chain]
  | i :: v => (mem_chain_cons i v _).2 (Or.inr (Or.inr ⟨v, self_mem v, rfl⟩))

lemma chain_nil : chain [] = {[]} := rfl

/-- generalized minimality: only prefix and sibling closure are needed -/
lemma chain_sub_of (T : Finset Node)
    (hpre : ∀ x ∈ T, ∀ p, p.IsPrefix x → p ∈ T)
    (hsib : ∀ p i, p ++ [i] ∈ T → ∀ j, 0 < j → j ≤ i → p ++ [j] ∈ T) :
    ∀ (x p : Node), p ++ x ∈ T → ∀ y ∈ chain x, p ++ y ∈ T
  | [], p, h, y, hy => by
      rw [chain_nil, Finset.mem_singleton] at hy; subst hy; simpa using h
  | i :: v, p, h, y, hy => by
      rcases (mem_chain_cons i v y).1 hy with rfl | ⟨j, h1, h2, rfl⟩ | ⟨y', hy', rfl⟩
      · simpa using hpre _ h p (List.prefix_append _ _)
      · have hpi : p ++ [i] ∈ T := hpre _ h _ (by
          rw [show p ++ i :: v = (p ++ [i]) ++ v by simp]; exact List.prefix_append _ _)
        exact hsib p i hpi j (by omega) (by omega)
      · have := chain_sub_of T hpre hsib v (p ++ [i]) (by simpa using h) y' hy'
        simpa using this

lemma chain_prefix (x : Node) : ∀ a ∈ chain x, ∀ p, p.IsPrefix a → p ∈ chain x := by
    intro a ha p hp
    induction x generalizing a p with
    | nil =>
      rw [chain_nil, Finset.mem_singleton] at ha; subst ha
      rw [List.prefix_nil] at hp; subst hp; exact nil_mem _
    | cons i v ih =>
      rcases (mem_chain_cons i v a).1 ha with rfl | ⟨j, h1, h2, rfl⟩ | ⟨a', ha', rfl⟩
      · rw [List.prefix_nil] at hp; subst hp; exact nil_mem _
      · rcases List.prefix_cons_iff.1 hp with rfl | ⟨p', rfl, hp'⟩
        · exact nil_mem _
        · rw [List.prefix_nil] at hp'; subst hp'
          exact (mem_chain_cons i v _).2 (Or.inr (Or.inl ⟨j, h1, h2, rfl⟩))
      · rcases List.prefix_cons_iff.1 hp with rfl | ⟨p', rfl, hp'⟩
        · exact nil_mem _
        · exact (mem_chain_cons i v _).2 (Or.inr (Or.inr ⟨p', ih a' ha' p' hp', rfl⟩))
lemma chain_sib (x : Node) :
    ∀ p i, p ++ [i] ∈ chain x → ∀ j, 0 < j → j ≤ i → p ++ [j] ∈ chain x := by
    intro p k hk j hj hjk
    induction x generalizing p with
    | nil => rw [chain_nil, Finset.mem_singleton] at hk; simp at hk
    | cons i v ih =>
      rcases (mem_chain_cons i v _).1 hk with h | ⟨l, h1, h2, h⟩ | ⟨y', hy', h⟩
      · simp at h
      · cases p with
        | nil =>
          simp at h; subst h
          exact (mem_chain_cons i v _).2 (Or.inr (Or.inl ⟨j, by omega, by omega, rfl⟩))
        | cons a p' => simp at h
      · cases p with
        | nil =>
          simp at h; obtain ⟨rfl, rfl⟩ := h
          by_cases hji : j = k
          · subst hji
            exact (mem_chain_cons j v _).2 (Or.inr (Or.inr ⟨[], nil_mem v, rfl⟩))
          · exact (mem_chain_cons k v _).2 (Or.inr (Or.inl ⟨j, by omega, by omega, rfl⟩))
        | cons a p' =>
          simp at h; obtain ⟨rfl, rfl⟩ := h
          exact (mem_chain_cons a v _).2 (Or.inr (Or.inr ⟨p' ++ [j], ih p' hy', rfl⟩))
lemma chain_sub (x y : Node) (hy : y ∈ chain x) : chain y ⊆ chain x := by
  intro z hz
  have := chain_sub_of (chain x) (chain_prefix x) (chain_sib x) y [] (by simpa using hy) z hz
  simpa using this


lemma chain_pos : ∀ x : Node, Positive x → ∀ y ∈ chain x, Positive y
  | [], _, y, hy => by rw [chain_nil, Finset.mem_singleton] at hy; subst hy; intro i hi; simp at hi
  | i :: v, hx, y, hy => by
      have hi : 0 < i := hx i (by simp)
      have hv : Positive v := fun k hk => hx k (by simp [hk])
      rcases (mem_chain_cons i v y).1 hy with rfl | ⟨j, h1, h2, rfl⟩ | ⟨y', hy', rfl⟩
      · intro k hk; simp at hk
      · intro k hk; simp at hk; omega
      · intro k hk
        rcases List.mem_cons.1 hk with rfl | hk
        · exact hi
        · exact chain_pos v hv y' hy' k hk

lemma weight_lt : ∀ x : Node, Positive x → ∀ y ∈ chain x, y ≠ x → weight y < weight x
  | [], _, y, hy, hne => by rw [chain_nil, Finset.mem_singleton] at hy; exact absurd hy hne
  | i :: v, hx, y, hy, hne => by
      have hi : 0 < i := hx i (by simp)
      have hv : Positive v := fun k hk => hx k (by simp [hk])
      rcases (mem_chain_cons i v y).1 hy with rfl | ⟨j, h1, h2, rfl⟩ | ⟨y', hy', rfl⟩
      · simp [weight]; omega
      · simp [weight]; omega
      · have hne' : y' ≠ v := fun h => hne (by rw [h])
        have := weight_lt v hv y' hy' hne'
        simp [weight] at this ⊢; omega

lemma last_chain : ∀ x : Node, ∀ y ∈ chain x, y = x ∨ PreLt y x
  | [], y, hy => by rw [chain_nil, Finset.mem_singleton] at hy; exact Or.inl hy
  | i :: v, y, hy => by
      rcases (mem_chain_cons i v y).1 hy with rfl | ⟨j, h1, h2, rfl⟩ | ⟨y', hy', rfl⟩
      · exact Or.inr (Or.inl ⟨List.nil_prefix, by simp⟩)
      · exact Or.inr (Or.inr ⟨[], j, i, [], v, rfl, rfl, by omega⟩)
      · rcases last_chain v y' hy' with rfl | (⟨hp, hne⟩ | ⟨p, a, b, u, w, h1, h2, hab⟩)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨List.cons_prefix_cons.2 ⟨rfl, hp⟩, by simpa using hne⟩)
        · exact Or.inr (Or.inr ⟨i :: p, a, b, u, w, by simp [h1], by simp [h2], hab⟩)

lemma ordered_chain (x : Node) (hx : Positive x) : Ordered (chain x) :=
  ⟨chain_pos x hx, chain_prefix x, chain_sib x⟩

lemma ordered_union (S T : Finset Node) (hS : Ordered S) (hT : Ordered T) : Ordered (S ∪ T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx; rcases Finset.mem_union.1 hx with h | h
    · exact hS.1 x h
    · exact hT.1 x h
  · intro x hx p hp; rcases Finset.mem_union.1 hx with h | h
    · exact Finset.mem_union_left _ (hS.2.1 x h p hp)
    · exact Finset.mem_union_right _ (hT.2.1 x h p hp)
  · intro p i hx j hj hji; rcases Finset.mem_union.1 hx with h | h
    · exact Finset.mem_union_left _ (hS.2.2 p i h j hj hji)
    · exact Finset.mem_union_right _ (hT.2.2 p i h j hj hji)

lemma last_leaf_youngest (T : Finset Node) (z : Node) (hT : Ordered T) (hz : Last T z) :
    Leaf T z ∧ (z ≠ [] → Youngest T z) := by
  obtain ⟨hzT, hlast⟩ := hz
  refine ⟨⟨hzT, ?_⟩, ?_⟩
  · rw [children, Finset.filter_eq_empty_iff]
    rintro y hy ⟨i, rfl⟩
    rcases hlast _ hy with h | (⟨hp, -⟩ | ⟨p, a, b, u, w, h1, h2, hab⟩)
    · have := congrArg List.length h; simp at this
    · have := hp.length_le; simp at this
    · rw [h2, List.append_assoc] at h1
      have := List.append_cancel_left h1
      simp at this; omega
  · intro hne
    obtain ⟨p, i, rfl⟩ : ∃ p i, z = p ++ [i] := by
      rcases List.eq_nil_or_concat' z with h | ⟨L, b, h⟩
      · exact absurd h hne
      · exact ⟨L, b, h⟩
    have hipos : 0 < i := hT.1 _ hzT i (by simp)
    refine ⟨p, i, rfl, hipos, ?_⟩
    have hmem : p ++ [i] ∈ children T p := by
      rw [children, Finset.mem_filter]; exact ⟨hzT, i, rfl⟩
    apply le_antisymm
    · have : id ((p ++ [i]).getLast!) ≤ degree T p := by
        unfold degree
        exact Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hmem)
      have hgl : (p ++ [i]).getLast! = i := by
        rw [List.getLast!_eq_getLast?_getD]; simp
      simpa [hgl] using this
    · unfold degree
      apply Finset.sup_le
      intro b hb
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb
      rw [children, Finset.mem_filter] at hy
      obtain ⟨hyT, k, rfl⟩ := hy
      have hgl : (p ++ [k]).getLast! = k := by
        rw [List.getLast!_eq_getLast?_getD]; simp
      simp only [id, hgl]
      by_contra hki
      push_neg at hki
      rcases hlast _ hyT with h | (⟨hp, hne'⟩ | ⟨q, a, c, u, w, h1, h2, hac⟩)
      · simp at h; omega
      · have := hp.eq_of_length (by simp); exact hne' this
      · have hl := congrArg List.length h1
        simp at hl
        rcases Nat.lt_or_ge q.length p.length with hq | hq
        · have e1 := congrArg (fun l => l[q.length]?) h1
          have e2 := congrArg (fun l => l[q.length]?) h2
          simp only [List.getElem?_append_left (by simpa using hq : q.length < p.length)] at e1 e2
          simp at e1 e2
          rw [e1] at e2; simp at e2; omega
        · have hqe : q.length = p.length := by omega
          have e1 := congrArg (fun l => l[q.length]?) h1
          have e2 := congrArg (fun l => l[q.length]?) h2
          simp [hqe] at e1 e2
          omega

end BuchiRabinIndex.LowerBound.Fact30Aux

open BuchiRabinIndex.LowerBound BuchiRabinIndex.LowerBound.Fact30Aux in
theorem solution (x y : Node) (hx : Positive x) (hy : Positive y) :
    (Prec y x → PreLt y x) ∧ Last (chain x) x ∧
    (y ∈ chain x → chain y ⊆ chain x) ∧
    (x ∈ chain y → y ∈ chain x → x = y) ∧
    Ordered (chain x) ∧
    (∀ T, Ordered T → x ∈ T → chain x ⊆ T) ∧
    Ordered (chain x ∪ chain y) ∧
    (x ≠ [] → ({[], [1]} : Finset Node) ⊆ chain x) ∧
    (∀ T z, Ordered T → Last T z → Leaf T z ∧ (z ≠ [] → Youngest T z)) := by
  refine ⟨?_, ⟨self_mem x, last_chain x⟩, chain_sub x y, ?_, ordered_chain x hx, ?_,
    ordered_union _ _ (ordered_chain x hx) (ordered_chain y hy), ?_,
    fun T z hT hz => last_leaf_youngest T z hT hz⟩
  · rintro ⟨p, i, v, rfl, h | ⟨j, hj0, hji, rfl⟩⟩
    · subst h
      refine Or.inl ⟨List.prefix_append _ _, ?_⟩
      intro h; have := congrArg List.length h; simp at this
    · exact Or.inr ⟨p, j, i, [], v, rfl, rfl, hji⟩
  · intro hxy hyx
    by_contra hne
    have h1 := weight_lt y hy x hxy hne
    have h2 := weight_lt x hx y hyx (Ne.symm hne)
    omega
  · intro T hT hxT z hz
    have := chain_sub_of T hT.2.1 hT.2.2 x [] (by simpa using hxT) z hz
    simpa using this
  · intro hne
    obtain ⟨i, v, rfl⟩ : ∃ i v, x = i :: v := by
      cases x with
      | nil => exact absurd rfl hne
      | cons i v => exact ⟨i, v, rfl⟩
    have hi : 0 < i := hx i (by simp)
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact nil_mem _
    · by_cases h1 : i = 1
      · subst h1; exact (mem_chain_cons 1 v _).2 (Or.inr (Or.inr ⟨[], nil_mem v, rfl⟩))
      · exact (mem_chain_cons i v _).2 (Or.inr (Or.inl ⟨1, le_rfl, by omega, rfl⟩))
