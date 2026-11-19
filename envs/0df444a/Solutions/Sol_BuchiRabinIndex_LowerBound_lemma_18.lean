-- Prove2me | solution 1 for BuchiRabinIndex.LowerBound.lemma_18
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T16:30:28.795623+00:00
-- url     : https://prove2.me/submissions/b3355622-55be-4c81-a8b4-f0b2149464e6

import Definitions.Def_BuchiRabinIndex_LowerBound_Nodes

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound.Lemma18Aux
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


lemma pos_bw (b : ℕ) : ∀ (d : ℕ) (x : Node), x ∈ boundedWords b d → Positive x
  | 0, x, hx => by simp [boundedWords] at hx; subst hx; intro i hi; simp at hi
  | d + 1, x, hx => by
      simp only [boundedWords, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_Icc,
        Finset.mem_image] at hx
      rcases hx with rfl | ⟨j, hj, u, hu, rfl⟩
      · intro i hi; simp at hi
      · intro i hi
        rcases List.mem_cons.1 hi with rfl | hi
        · omega
        · exact pos_bw b d u hu i hi

lemma pos_of_mem_fullTree (n : ℕ) (x : Node) (hx : x ∈ fullTree n) : Positive x := by
  unfold fullTree at hx
  split_ifs at hx
  · simp at hx
  · exact pos_bw _ _ x (Finset.mem_filter.1 hx).1


lemma chain_one (v : Node) : chain (1 :: v) = insert [] ((chain v).image (1 :: ·)) := by
  ext z; rw [mem_chain_cons, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (h | ⟨j, h1, h2, -⟩ | ⟨y', hy', rfl⟩)
    · exact Or.inl h
    · omega
    · exact Or.inr ⟨y', hy', rfl⟩
  · rintro (h | ⟨y', hy', rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨y', hy', rfl⟩)

lemma inc_inj : Function.Injective increment := by
  intro a b h
  cases a <;> cases b <;> simp_all [increment]

lemma chain_inc (i : ℕ) (hi : 1 ≤ i) (v : Node) :
    chain ((i + 1) :: v) = insert [1] ((chain (i :: v)).image increment) := by
  ext z; rw [Finset.mem_insert, Finset.mem_image, mem_chain_cons]
  constructor
  · rintro (rfl | ⟨j, h1, h2, rfl⟩ | ⟨y', hy', rfl⟩)
    · exact Or.inr ⟨[], nil_mem _, rfl⟩
    · by_cases hj : j = 1
      · exact Or.inl (by rw [hj])
      · refine Or.inr ⟨[j - 1], (mem_chain_cons i v _).2 (Or.inr (Or.inl ⟨j - 1, by omega,
          by omega, rfl⟩)), ?_⟩
        simp [increment]; omega
    · exact Or.inr ⟨i :: y', (mem_chain_cons i v _).2 (Or.inr (Or.inr ⟨y', hy', rfl⟩)),
        by simp [increment]⟩
  · rintro (rfl | ⟨y, hy, rfl⟩)
    · exact Or.inr (Or.inl ⟨1, le_rfl, by omega, rfl⟩)
    · rcases (mem_chain_cons i v y).1 hy with rfl | ⟨j, h1, h2, rfl⟩ | ⟨y', hy', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨j + 1, by omega, by omega, by simp [increment]⟩)
      · exact Or.inr (Or.inr ⟨y', hy', by simp [increment]⟩)

lemma card_chain : ∀ x : Node, Positive x → (chain x).card = weight x + 1
  | [], _ => by simp [chain, weight]
  | i :: v, hx => by
      have hi : 0 < i := hx i (by simp)
      have hv : Positive v := fun k hk => hx k (by simp [hk])
      have ih := card_chain v hv
      have hdisj : Disjoint ((Finset.Icc 1 (i - 1)).image fun j => [j])
          ((chain v).image (i :: ·)) := by
        rw [Finset.disjoint_left]
        intro a ha hb
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 ha
        obtain ⟨y, -, hy⟩ := Finset.mem_image.1 hb
        simp at hy hj; omega
      have hnil : [] ∉ ((Finset.Icc 1 (i - 1)).image fun j => [j]) ∪ ((chain v).image (i :: ·)) := by
        simp
      simp only [chain]
      rw [Finset.card_insert_of_notMem hnil, Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective _ (fun a b h => by simpa using h),
        Finset.card_image_of_injective _ (fun a b h => by simpa using h), ih]
      simp [weight]; omega

lemma mem_fullTree (n : ℕ) (hn : 1 ≤ n) (x : Node) :
    x ∈ fullTree n ↔ Positive x ∧ x.sum ≤ n - 1 := by
  have hn0 : n ≠ 0 := by omega
  have hft : fullTree n = (boundedWords (n - 1) (n - 1)).filter (weight · ≤ n - 1) := by
    unfold fullTree; exact if_neg hn0
  rw [hft, Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨pos_bw _ _ x h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    clear hft
    -- membership in boundedWords
    have key : ∀ (b d : ℕ) (x : Node), (∀ i ∈ x, 1 ≤ i ∧ i ≤ b) → x.length ≤ d →
        x ∈ boundedWords b d := by
      intro b d
      induction d with
      | zero => intro x _ hl; simp at hl; subst hl; simp [boundedWords]
      | succ d ih =>
        intro x hb hl
        cases x with
        | nil => simp [boundedWords]
        | cons a t =>
          simp only [boundedWords, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_Icc,
            Finset.mem_image]
          right
          exact ⟨a, hb a (by simp), t, ih t (fun i hi => hb i (by simp [hi]))
            (by simp at hl; omega), rfl⟩
    have hsum : ∀ (x : List ℕ) (i : ℕ), i ∈ x → i ≤ x.sum := by
      intro x; induction x with
      | nil => simp
      | cons a t ih => intro i hi; rcases List.mem_cons.1 hi with rfl | hi
                       · simp
                       · have := ih i hi; simp; omega
    have hlen : ∀ (x : List ℕ), Positive x → x.length ≤ x.sum := by
      intro x; induction x with
      | nil => simp
      | cons a t ih => intro hp; have := ih (fun k hk => hp k (by simp [hk]))
                       have := hp a (by simp); simp; omega
    exact key _ _ x (fun i hi => ⟨h1 i hi, (hsum x i hi).trans (by simpa [weight] using h2)⟩)
      ((hlen x h1).trans (by simpa [weight] using h2))

end BuchiRabinIndex.LowerBound.Lemma18Aux



open BuchiRabinIndex.LowerBound BuchiRabinIndex.LowerBound.Lemma18Aux in
theorem solution (n : ℕ) (hn : 2 ≤ n) (x y : Node)
    (hx : x ∈ fullTree n) (hy : y ∈ fullTree n) (hne : x ≠ y) :
    (x ∈ part1 n → y ∈ part1 n →
      (chain x ∪ chain y).card = (chain (phi1 x) ∪ chain (phi1 y)).card + 1) ∧
    (x ∈ part2 n → y ∈ part2 n →
      (chain x ∪ chain y).card = (chain (phi2 x) ∪ chain (phi2 y)).card + 1) ∧
    ((x ∈ part1 n ∧ y ∈ part2 n) ∨ (x ∈ part2 n ∧ y ∈ part1 n) →
      chain x ∩ chain y = {[], [1]} ∧
      (chain x ∪ chain y).card = weight x + weight y ∧
      ∀ w, weight x = w → weight y = w → (chain x ∪ chain y).card = 2 * w) := by
  classical
  have px := pos_of_mem_fullTree n x hx
  have py := pos_of_mem_fullTree n y hy
  have M' := mem_fullTree (n - 1) (by omega)
  have hp1 : ∀ z, z ∈ part1 n → ∃ v, z = 1 :: v := by
    intro z hz; simp only [part1, Finset.mem_image] at hz
    obtain ⟨v, -, rfl⟩ := hz; exact ⟨v, rfl⟩
  have hp2 : ∀ z, z ∈ part2 n → ∃ i v, 1 ≤ i ∧ z = (i + 1) :: v := by
    intro z hz; simp only [part2, Finset.mem_image, Finset.mem_erase] at hz
    obtain ⟨u, ⟨hu0, hu⟩, rfl⟩ := hz
    cases u with
    | nil => exact absurd rfl hu0
    | cons i v =>
      have := ((M' _).1 hu).1 i (by simp)
      exact ⟨i, v, this, by simp [increment]⟩
  -- the mixed case, stated for x in part1 and y in part2
  have mixed : ∀ a b : Node, Positive a → Positive b → a ∈ part1 n → b ∈ part2 n →
      chain a ∩ chain b = {[], [1]} ∧ (chain a ∪ chain b).card = weight a + weight b := by
    intro a b pa pb ha hb
    obtain ⟨v, rfl⟩ := hp1 a ha
    obtain ⟨k, v', hk, rfl⟩ := hp2 b hb
    have hint : chain (1 :: v) ∩ chain ((k + 1) :: v') = {[], [1]} := by
      ext z
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      rw [mem_chain_cons, mem_chain_cons]
      constructor
      · rintro ⟨h1 | ⟨j, hj1, hj2, -⟩ | ⟨y', -, rfl⟩, h2 | ⟨j, hj1', hj2', h⟩ | ⟨y'', -, h⟩⟩
        all_goals first | exact Or.inl h1 | omega | (simp at h ⊢; try omega) | skip
        all_goals first | exact h.2 | simp at h2
      · rintro (rfl | rfl)
        · exact ⟨Or.inl rfl, Or.inl rfl⟩
        · exact ⟨Or.inr (Or.inr ⟨[], nil_mem v, rfl⟩),
            Or.inr (Or.inl ⟨1, le_rfl, by omega, rfl⟩)⟩
    refine ⟨hint, ?_⟩
    have hc := Finset.card_union_add_card_inter (chain (1 :: v)) (chain ((k + 1) :: v'))
    rw [hint, card_chain _ pa, card_chain _ pb] at hc
    have : ({[], [1]} : Finset Node).card = 2 := by decide
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro hx1 hy1
    obtain ⟨v, rfl⟩ := hp1 x hx1
    obtain ⟨v', rfl⟩ := hp1 y hy1
    simp only [phi1, List.tail_cons]
    rw [chain_one, chain_one, ← Finset.insert_union_distrib, ← Finset.image_union,
      Finset.card_insert_of_notMem (by simp),
      Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  · intro hx2 hy2
    obtain ⟨i, v, hi, rfl⟩ := hp2 x hx2
    obtain ⟨k, v', hk, rfl⟩ := hp2 y hy2
    simp only [phi2, Nat.add_sub_cancel]
    rw [chain_inc i hi, chain_inc k hk, ← Finset.insert_union_distrib, ← Finset.image_union,
      Finset.card_insert_of_notMem, Finset.card_image_of_injective _ inc_inj]
    rw [Finset.mem_image]
    rintro ⟨z, hz, hzi⟩
    have hpz : Positive z := by
      rcases Finset.mem_union.1 hz with h | h
      · exact chain_pos _ (fun j hj => by
          rcases List.mem_cons.1 hj with rfl | hj
          · omega
          · exact px j (by simp [hj])) z h
      · exact chain_pos _ (fun j hj => by
          rcases List.mem_cons.1 hj with rfl | hj
          · omega
          · exact py j (by simp [hj])) z h
    cases z with
    | nil => simp [increment] at hzi
    | cons a t =>
      simp [increment] at hzi
      have := hpz a (by simp); omega
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · obtain ⟨hi, hc⟩ := mixed x y px py h1 h2
      exact ⟨hi, hc, fun w hw1 hw2 => by omega⟩
    · obtain ⟨hi, hc⟩ := mixed y x py px h2 h1
      refine ⟨by rw [Finset.inter_comm]; exact hi, by rw [Finset.union_comm]; omega,
        fun w hw1 hw2 => by rw [Finset.union_comm]; omega⟩
